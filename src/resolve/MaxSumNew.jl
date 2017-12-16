# This file is a part of Julia. License is MIT: https://julialang.org/license

module MaxSum

include("FieldValues.jl")

using .FieldValues, ..VersionWeights, ...Types

export UnsatError, Messages, maxsum

# An exception type used internally to signal that an unsatisfiable
# constraint was detected
struct UnsatError <: Exception
    info
end

# Some parameters to drive the decimation process
mutable struct MaxSumParams
    nondec_iterations # number of initial iterations before starting
                      # decimation
    dec_interval # number of iterations between decimations
    dec_fraction # fraction of nodes to decimate at every decimation
                 # step

    function MaxSumParams()
        accuracy = parse(Int, get(ENV, "JULIA_PKGRESOLVE_ACCURACY", "1"))
        if accuracy <= 0
            error("JULIA_PKGRESOLVE_ACCURACY must be > 0")
        end
        nondec_iterations = accuracy * 20
        dec_interval = accuracy * 10
        dec_fraction = 0.05 / accuracy
        return new(nondec_iterations, dec_interval, dec_fraction)
    end
end

# Messages has the cavity messages and the total fields, and
# gets updated iteratively (and occasionally decimated) until
# convergence
mutable struct Messages
    # cavity incoming messages: for each package p0,
    #                           for each neighbor p1 of p0,
    #                           msg[p0][p1] is a vector of length spp[p0]
    #                           messages are normalized (i.e. the max is always 0)
    msg::Vector{Vector{Field}}

    # overall fields: for each package p0,
    #                 fld[p0] is a vector of length spp[p0]
    #                 fields are not normalized
    fld::Vector{Field}

    # backup of the initial value of fld, to be used when resetting
    initial_fld::Vector{Field}

    # keep track of which variables have been decimated
    decimated::BitVector
    num_nondecimated::Int

    function Messages(graph::NewGraph)
        np = graph.np
        spp = graph.spp
        gconstr = graph.gconstr
        req_inds = graph.req_inds
        pvers = graph.data.pvers
        pdict = graph.data.pdict

        ## generate wveights (v0 == spp[p0] is the "uninstalled" state)
        vweight = [[VersionWeight(v0 < spp[p0] ? pvers[p0][v0] : v"0") for v0 = 1:spp[p0]] for p0 = 1:np]

        # external fields: favor newest versions over older, and no-version over all
        fld = [[FieldValue(0, zero(VersionWeight), vweight[p0][v0], (v0==spp[p0]), 0) for v0 = 1:spp[p0]] for p0 = 1:np]

        # enforce constraints
        for p0 = 1:np
            fld0 = fld[p0]
            gconstr0 = gconstr[p0]
            for v0 = 1:spp[p0]
                gconstr0[v0] || (fld0[v0] = FieldValue(-1))
            end
        end

        # favor explicit requirements
        for rp0 in req_inds
            fld0 = fld[rp0]
            gconstr0 = gconstr[rp0]
            for v0 = 1:spp[rp0]-1
                gconstr0[v0] || continue
                # the state is one of those explicitly requested:
                # favor it at a higer level than normal (upgrade
                # FieldValue from l2 to l1)
                fld0[v0] += FieldValue(0, vweight[rp0][v0], -vweight[rp0][v0])
            end
        end

        # normalize fields
        for p0 = 1:np
            fld[p0] .-= maximum(fld[p0])
        end

        initial_fld = [copy(f0) for f0 in fld]

        # initialize cavity messages to 0
        gadj = graph.gadj
        msg = [[zeros(FieldValue, spp[p0]) for j1 = 1:length(gadj[p0])] for p0 = 1:np]

        return new(msg, fld, initial_fld, falses(np), np)
    end
end

function getsolution(msgs::Messages)
    # the solution is just the location of the maximum in
    # each field

    fld = msgs.fld
    np = length(fld)
    sol = Vector{Int}(np)
    for p0 = 1:np
        fld0 = fld[p0]
        s0 = indmax(fld0)
        if !validmax(fld0[s0])
            throw(UnsatError(p0))
        end
        sol[p0] = s0
    end
    return sol
end

# This is the core of the max-sum solver:
# for a given node p0 (i.e. a package) updates all
# input cavity messages and fields of its neighbors
function update(p0::Int, graph::NewGraph, msgs::Messages)
    gadj = graph.gadj
    gmsk = graph.gmsk
    gdir = graph.gdir
    adjdict = graph.adjdict
    spp = graph.spp
    np = graph.np
    msg = msgs.msg
    fld = msgs.fld
    decimated = msgs.decimated

    maxdiff = zero(FieldValue)

    gadj0 = gadj[p0]
    msg0 = msg[p0]
    fld0 = fld[p0]
    spp0 = spp[p0]
    adjdict0 = adjdict[p0]

    # iterate over all neighbors of p0
    for j0 in 1:length(gadj0)

        p1 = gadj0[j0]
        decimated[p1] && continue
        j1 = adjdict0[p1]
        #@assert j0 == adjdict[p1][p0]
        bm1 = gmsk[p1][j1]
        dir1 = gdir[p1][j1]
        spp1 = spp[p1]
        msg1 = msg[p1]

        # compute the output cavity message p0->p1
        cavmsg = fld0 - msg0[j0]

        if dir1 == Types.BACKWARDS
            # p0 depends on p1
            for v0 = 1:spp0-1
                cavmsg[v0] += FieldValue(0, VersionWeight(0), VersionWeight(0), 0, v0)
            end
        end

        # keep the old input cavity message p0->p1
        oldmsg = msg1[j1]

        # init the new message to minus infinity
        newmsg = [FieldValue(-1) for v1 = 1:spp1]

        # compute the new message by passing cavmsg
        # through the constraint encoded in the bitmask
        # (nearly equivalent to:
        #    newmsg = [maximum(cavmsg[bm1[:,v1]]) for v1 = 1:spp1]
        #  except for the directional term)
        m = FieldValue(-1)
        for v1 = 1:spp1
            for v0 = 1:spp0
                if bm1[v0, v1]
                    newmsg[v1] = max(newmsg[v1], cavmsg[v0])
                end
            end
            if dir1 == Types.FORWARD && v1 != spp1
                # p1 depends on p0
                newmsg[v1] += FieldValue(0, VersionWeight(0), VersionWeight(0), 0, v1)
            end
            m = max(m, newmsg[v1])
        end
        if !validmax(m)
            # No state available without violating some
            # hard constraint
            throw(UnsatError(p1))
        end

        # normalize the new message
        for v1 = 1:spp1
            newmsg[v1] -= m
        end

        diff = newmsg - oldmsg
        maxdiff = max(maxdiff, maximum(abs.(diff)))

        # update the field of p1
        fld1 = fld[p1]
        for v1 = 1:spp1
            fld1[v1] += diff[v1]
        end

        # put the newly computed message in place
        msg1[j1] = newmsg
    end
    return maxdiff
end

# A simple shuffling machinery for the update order in iterate()
# (wouldn't pass any random quality test but it's arguably enough)
mutable struct NodePerm
    p::Vector{Int}
    step::Int64
    NodePerm(np::Integer) = new(collect(1:np), 1)
end

function Base.shuffle!(perm::NodePerm)
    p = perm.p
    for j = length(p):-1:2
        k = perm.step % j + 1
        p[j], p[k] = p[k], p[j]
        perm.step += isodd(j) ? 1 : k
    end
    #@assert isperm(p)
end

Base.start(perm::NodePerm) = start(perm.p)
Base.next(perm::NodePerm, x) = next(perm.p, x)
Base.done(perm::NodePerm, x) = done(perm.p, x)

# Call update for all nodes (i.e. packages) in
# random order
function iterate(graph::NewGraph, msgs::Messages, perm::NodePerm)
    maxdiff = zero(FieldValue)
    shuffle!(perm)
    for p0 in perm
        maxdiff0 = update(p0, graph, msgs)
        maxdiff = max(maxdiff, maxdiff0)
    end
    return maxdiff
end

function decimate1(p0::Int, graph::NewGraph, msgs::Messages)
    decimated = msgs.decimated
    fld = msgs.fld
    adjdict = graph.adjdict
    gmsk = graph.gmsk

    @assert !decimated[p0]
    fld0 = fld[p0]
    s0 = indmax(fld0)
    # only do the decimation if it is consistent with
    # the previously decimated nodes
    for p1 in find(decimated)
        haskey(adjdict[p0], p1) || continue
        s1 = indmax(fld[p1])
        j1 = adjdict[p0][p1]
        gmsk[p1][j1][s0,s1] || return false
    end
    #println("DECIMATING $p0 (s0=$s0 fld=$fld0)")
    for v0 = 1:length(fld0)
        v0 == s0 && continue
        fld0[v0] = FieldValue(-1)
    end
    msgs.decimated[p0] = true
    msgs.num_nondecimated -= 1
    return true
end

function reset_messages!(msgs::Messages)
    msg = msgs.msg
    fld = msgs.fld
    initial_fld = msgs.initial_fld
    decimated = msgs.decimated
    np = length(fld)
    for p0 = 1:np
        map(m->fill!(m, zero(FieldValue)), msg[p0])
        decimated[p0] && continue
        fld[p0] = copy(initial_fld[p0])
    end
    return msgs
end

# If normal convergence fails (or is too slow) fix the most
# polarized packages by adding extra infinite fields on every state
# but the maximum
function decimate(n::Int, graph::NewGraph, msgs::Messages)
    #println("DECIMATING $n NODES")
    adjdict = graph.adjdict
    fld = msgs.fld
    decimated = msgs.decimated
    fldorder = sortperm(fld, by=secondmax)
    did_dec = false
    for p0 in fldorder
        decimated[p0] && continue
        did_dec |= decimate1(p0, graph, msgs)
        n -= 1
        n == 0 && break
    end
    @assert n == 0
    if !did_dec
        # did not succeed in decimating anything;
        # try to decimate at least one node
        for p0 in fldorder
            decimated[p0] && continue
            if decimate1(p0, graph, msgs)
                did_dec = true
                break
            end
        end
    end
    if !did_dec
        # still didn't succeed, give up
        p0 = first(fldorder[.~(decimated)])
        throw(UnsatError(p0))
    end

    reset_messages!(msgs)
    return
end

# In case ties still exist at convergence, break them and
# keep converging
function break_ties(msgs::Messages)
    fld = msgs.fld
    unbroken_ties = Int[]
    for p0 = 1:length(fld)
        fld0 = fld[p0]
        z = 0
        m = typemin(FieldValue)
        for v0 = 1:length(fld0)
            if fld0[v0] > m
                m = fld0[v0]
                z = 1
            elseif fld0[v0] == m
                z += 1
            end
        end
        if z > 1
            #println("TIE! p0=$p0")
            decimate1(p0, msgs) && return false
            push!(unbroken_ties, p0)
        end
    end
    # If there were ties, but none were broken, bail out
    isempty(unbroken_ties) || throw(PkgError(first(unbroken_ties)))
    return true
end

# Iterative solver: run iterate() until convergence
# (occasionally calling decimate())
function maxsum(graph::NewGraph, msgs::Messages)
    params = MaxSumParams()

    it = 0
    perm = NodePerm(graph.np)
    while true
        it += 1
        maxdiff = iterate(graph, msgs, perm)
        #println("it = $it maxdiff = $maxdiff")

        if maxdiff == zero(FieldValue)
            break_ties(msgs) && break
            continue
        end
        if it >= params.nondec_iterations &&
           (it - params.nondec_iterations) % params.dec_interval == 0
            numdec = clamp(floor(Int, params.dec_fraction * graph.np), 1, msgs.num_nondecimated)
            decimate(numdec, graph, msgs)
            msgs.num_nondecimated == 0 && break
        end
    end

    # Finally, decimate everything just to
    # check against inconsistencies
    # (old_numnondec is saved just to prevent
    # wrong messages about accuracy)
    old_numnondec = msgs.num_nondecimated
    decimate(msgs.num_nondecimated, graph, msgs)
    msgs.num_nondecimated = old_numnondec

    return getsolution(msgs)
end

end
