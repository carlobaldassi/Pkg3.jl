# This file is a part of Julia. License is MIT: https://julialang.org/license

module GraphType

using ..Types
import ..Types.uuid_julia
import Pkg3.equalto

export NewGraph, add_reqs!, add_fixed!, simplify_graph!

mutable struct GraphData
    # packages list
    pkgs::Vector{UUID}

    # number of packages
    np::Int

    # states per package: one per version + uninstalled
    spp::Vector{Int}

    # pakage dict: associates an index to each package id
    pdict::Dict{UUID,Int}

    # package versions: for each package, keep the list of the
    #                   possible version numbers; this defines a
    #                   mapping from version numbers of a package
    #                   to indices
    pvers::Vector{Vector{VersionNumber}}

    # versions dict: associates a version index to each package
    #                version; such that
    #                  pvers[p0][vdict[p0][vn]] = vn
    vdict::Vector{Dict{VersionNumber,Int}}

    uuid_to_name::Dict{UUID,String}

    reqs::Requires
    fixed::Dict{UUID,Fixed}

    # pruned packages: during graph simplification, packages that
    #                  only have one allowed version are pruned.
    #                  This keeps track of them, so that they may
    #                  be returned in the solution (unless they
    #                  were explicitly fixed)
    pruned::Dict{UUID,VersionNumber}

    function GraphData(
            versions::Dict{UUID,Set{VersionNumber}},
            deps::Dict{UUID,Dict{VersionRange,Dict{String,UUID}}},
            compat::Dict{UUID,Dict{VersionRange,Dict{String,VersionSpec}}},
            uuid_to_name::Dict{UUID,String},
            reqs::Requires,
            fixed::Dict{UUID,Fixed}
        )
        # generate pkgs
        pkgs = sort!(collect(keys(versions)))
        np = length(pkgs)

        # generate pdict
        pdict = Dict{UUID,Int}(pkgs[p0] => p0 for p0 = 1:np)

        # generate spp and pvers
        pvers = [sort!(collect(versions[pkgs[p0]])) for p0 = 1:np]
        spp = length.(pvers) .+ 1

        # generate vdict
        vdict = [Dict{VersionNumber,Int}(vn => i for (i,vn) in enumerate(pvers[p0])) for p0 = 1:np]

        pruned = Dict{UUID,VersionNumber}()

        return new(pkgs, np, spp, pdict, pvers, vdict, uuid_to_name, reqs, fixed, pruned)
    end
end

@enum DepDir FORWARD BACKWARDS BIDIR NONE

function update_depdir(dd0::DepDir, dd1::DepDir)
    dd0 == dd1 && return dd0
    dd0 == NONE && return dd1
    dd1 == NONE && return dd0
    return BIDIR
end

mutable struct NewGraph
    # data:
    #   stores all the structures required to map between
    #   parsed items (names, UUIDS, version numbers...) and
    #   the numeric representation used in the main Graph data
    #   structure.
    data::GraphData

    # adjacency matrix:
    #   for each package, has the list of neighbors
    #   indices
    gadj::Vector{Vector{Int}}

    # compatibility mask:
    #   for each package p0 has a list of bool masks.
    #   Each entry in the list gmsk[p0] is relative to the
    #   package p1 as read from gadj[p0].
    #   Each mask has dimension spp1 x spp0, where
    #   spp0 is the number of states of p0, and
    #   spp1 is the number of states of p1.
    gmsk::Vector{Vector{BitMatrix}}

    # dependency direction:
    #   keeps track of which direction the dependency goes.
    gdir::Vector{Vector{DepDir}}

    # constraints:
    #   a mask of allowed states for each package (e.g. to express
    #   requirements)
    gconstr::Vector{BitVector}

    # adjacency dict:
    #   allows one to retrieve the indices in gadj, so that
    #   gadj[p0][adjdict[p1][p0]] = p1
    #   ("At which index does package p1 appear in gadj[p0]?")
    adjdict::Vector{Dict{Int,Int}}

    # indices of the packages that were *explicitly* required
    #   used to favor their versions at resolution
    req_inds::Set{Int}

    # indices of the packages that were *explicitly* fixed
    #   used to avoid returning them in the solution
    fix_inds::Set{Int}

    # states per package: same as in GraphData
    spp::Vector{Int}

    # number of packages (all Vectors above have this length)
    np::Int

    function NewGraph(
            versions::Dict{UUID,Set{VersionNumber}},
            deps::Dict{UUID,Dict{VersionRange,Dict{String,UUID}}},
            compat::Dict{UUID,Dict{VersionRange,Dict{String,VersionSpec}}},
            uuid_to_name::Dict{UUID,String},
            reqs::Requires = Requires(),
            fixed::Dict{UUID,Fixed} = Dict{UUID,Fixed}(uuid_julia=>Fixed(VERSION))
        )

        extra_uuids = union(keys(reqs), keys(fixed), map(fx->keys(fx.requires), values(fixed))...)
        extra_uuids ⊆ keys(versions) || error("unknown UUID found in reqs/fixed") # TODO?

        data = GraphData(versions, deps, compat, uuid_to_name, reqs, fixed)
        pkgs, np, spp, pdict, pvers, vdict = data.pkgs, data.np, data.spp, data.pdict, data.pvers, data.vdict

        extended_deps = [[Dict{Int,BitVector}() for v0 = 1:(spp[p0]-1)] for p0 = 1:np]
        for p0 = 1:np, v0 = 1:(spp[p0]-1)
            n2u = Dict{String,UUID}()
            vn = pvers[p0][v0]
            for (vr,vrmap) in deps[pkgs[p0]]
                vn ∈ vr || continue
                for (name,uuid) in vrmap
                    # check conflicts ??
                    n2u[name] = uuid
                end
            end
            req = Dict{Int,VersionSpec}()
            for (vr,vrmap) in compat[pkgs[p0]]
                vn ∈ vr || continue
                for (name,vs) in vrmap
                    haskey(n2u, name) || error("Unknown package $name found in the compatibility requirements of $(pkgID(pkgs[p0], uuid_to_name))")
                    uuid = n2u[name]
                    p1 = pdict[uuid]
                    # check conflicts instead of intersecting?
                    # (intersecting is used by fixed packages though...)
                    req_p1 = get!(req, p1) do; VersionSpec() end
                    req[p1] = req_p1 ∩ vs
                end
            end
            # The remaining dependencies do not have compatibility constraints
            for uuid in values(n2u)
                get!(req, pdict[uuid]) do; VersionSpec() end
            end
            # Translate the requirements into bit masks
            # req_msk = Dict(p1 => BitArray(pvers[p1][v1] ∈ vs for v1 = 0:(spp[p1]-1)) for (p1,vs) in req)
            req_msk = Dict(p1 => (pvers[p1][1:(spp[p1]-1)] .∈ vs) for (p1,vs) in req)
            extended_deps[p0][v0] = req_msk
        end

        gadj = [Int[] for p0 = 1:np]
        gmsk = [BitMatrix[] for p0 = 1:np]
        gdir = [DepDir[] for p0 = 1:np]
        gconstr = [trues(spp[p0]) for p0 = 1:np]
        adjdict = [Dict{Int,Int}() for p0 = 1:np]

        for p0 = 1:np, v0 = 1:(spp[p0]-1), (p1,rmsk1) in extended_deps[p0][v0]
            j0 = get(adjdict[p1], p0, length(gadj[p0]) + 1)
            j1 = get(adjdict[p0], p1, length(gadj[p1]) + 1)

            @assert (j0 > length(gadj[p0]) && j1 > length(gadj[p1])) ||
                    (j0 ≤ length(gadj[p0]) && j1 ≤ length(gadj[p1]))

            if j0 > length(gadj[p0])
                push!(gadj[p0], p1)
                push!(gadj[p1], p0)
                j0 = length(gadj[p0])
                j1 = length(gadj[p1])

                adjdict[p1][p0] = j0
                adjdict[p0][p1] = j1

                bm = trues(spp[p1], spp[p0])
                bmt = bm'

                push!(gmsk[p0], bm)
                push!(gmsk[p1], bmt)

                push!(gdir[p0], FORWARD)
                push!(gdir[p1], BACKWARDS)
            else
                bm = gmsk[p0][j0]
                bmt = gmsk[p1][j1]
                gdir[p0][j0] = update_depdir(gdir[p0][j0], FORWARD)
                gdir[p1][j1] = update_depdir(gdir[p1][j1], BACKWARDS)
            end

            for v1 = 1:(spp[p1]-1)
                rmsk1[v1] && continue
                bm[v1, v0] = false
                bmt[v0, v1] = false
            end
            bm[end,v0] = false
            bmt[v0,end] = false
        end

        req_inds = Set{Int}()
        fix_inds = Set{Int}()

        graph = new(data, gadj, gmsk, gdir, gconstr, adjdict, req_inds, fix_inds, spp, np)

        add_reqs!(graph, reqs, explicit = true)
        add_fixed!(graph, fixed)

        @assert check_consistency(graph)
        check_constraints(graph)

        return graph
    end
end

"""
Add requirements to the graph, implemented as constraints.
The `explicit` keyword indicates whether these are considered user-defined
requirements, and are thus prioritized by the solver.
"""
function add_reqs!(graph::NewGraph, reqs::Requires; explicit::Bool = false)
    gconstr = graph.gconstr
    spp = graph.spp
    req_inds = graph.req_inds
    pdict = graph.data.pdict
    pvers = graph.data.pvers

    for (rp,rvs) in reqs
        haskey(pdict, rp) || error("unknown required package $(pkgID(rp, graph))")
        rp0 = pdict[rp]
        gconstr0 = gconstr[rp0]
        gconstr0[end] = false
        for rv0 = 1:(spp[rp0]-1)
            rvn = pvers[rp0][rv0]
            rvn ∈ rvs || (gconstr0[rv0] = false)
        end
        explicit && push!(req_inds, rp0)
    end
    # TODO: add reqs in GraphData
    return graph
end

"Add fixed packages to the graph, implemented as constraints, and their requirements."
function add_fixed!(graph::NewGraph, fixed::Dict{UUID,Fixed})
    gconstr = graph.gconstr
    spp = graph.spp
    fix_inds = graph.fix_inds
    pdict = graph.data.pdict
    vdict = graph.data.vdict

    for (fp,fx) in fixed
        haskey(pdict, fp) || error("unknown fixed package $(pkgID(fp, graph))")
        fp0 = pdict[fp]
        fv0 = vdict[fp0][fx.version]
        # disable all versions, but keep the fixed one as-is
        # (allows to detect contradicions with requirements)
        old_constr = gconstr[fp0][fv0]
        fill!(gconstr[fp0], false)
        gconstr[fp0][fv0] = old_constr
        push!(fix_inds, fp0)
        add_reqs!(graph, fx.requires)
    end
    # TODO: add fixed in GraphData
    return graph
end

Types.pkgID(p::UUID, graph::NewGraph) = pkgID(p, graph.data.uuid_to_name)

function check_consistency(graph::NewGraph)
    np = graph.np
    spp = graph.spp
    gadj = graph.gadj
    gmsk = graph.gmsk
    gdir = graph.gdir
    gconstr = graph.gconstr
    adjdict = graph.adjdict
    req_inds = graph.req_inds
    fix_inds = graph.fix_inds
    data = graph.data
    pkgs = data.pkgs
    pdict = data.pdict
    pvers = data.pvers
    vdict = data.vdict
    pruned = data.pruned

    @assert np ≥ 0
    for x in [spp, gadj, gmsk, gdir, gconstr, adjdict, pkgs, pdict, pvers, vdict]
        @assert length(x) == np
    end
    for p0 = 1:np
        @assert pdict[pkgs[p0]] == p0
        spp0 = spp[p0]
        @assert spp0 ≥ 2
        pvers0 = pvers[p0]
        vdict0 = vdict[p0]
        @assert length(pvers0) == spp0 - 1
        for v0 = 1:(spp0-1)
            @assert vdict0[pvers0[v0]] == v0
        end
        for (vn,v0) in vdict0
            @assert 1 ≤ v0 ≤ spp0-1
            @assert pvers0[v0] == vn
        end
        gconstr0 = gconstr[p0]
        @assert length(gconstr0) == spp0

        gadj0 = gadj[p0]
        gmsk0 = gmsk[p0]
        gdir0 = gdir[p0]
        adjdict0 = adjdict[p0]
        @assert length(gmsk0) == length(gadj0)
        @assert length(adjdict0) == length(gadj0)
        @assert length(gdir0) == length(gadj0)
        for (j0,p1) in enumerate(gadj0)
            @assert adjdict[p1][p0] == j0
            spp1 = spp[p1]
            @assert size(gmsk0[j0]) == (spp1,spp0)
            j1 = adjdict0[p1]
            gmsk1 = gmsk[p1]
            @assert gmsk1[j1] == gmsk0[j0]'
        end
    end
    for (p,p0) in pdict
        @assert 1 ≤ p0 ≤ np
        @assert pkgs[p0] == p
        @assert !haskey(pruned, p)
    end
    for p0 in req_inds
        @assert 1 ≤ p0 ≤ np
        @assert !gconstr[p0][end]
    end
    for p0 in fix_inds
        @assert 1 ≤ p0 ≤ np
        @assert !gconstr[p0][end]
        @assert count(gconstr[p0]) == 1
    end
    return true
end

# function init_resolve_backtrace(uuid_to_name::Dict{UUID,String}, reqs::Requires, fix::Dict{UUID,Fixed} = Dict{UUID,Fixed}())
#     bktrc = ResolveBacktrace(uuid_to_name)
#     for (p,f) in fix
#         bktrc[p] = ResolveBacktraceItem(:fixed, f.version)
#     end
#     for (p,vs) in reqs
#         bktrcp = get!(bktrc, p) do; ResolveBacktraceItem() end
#         push!(bktrcp, :required, vs)
#     end
#     return bktrc
# end

"Check for contradictions in the constraints."
function check_constraints(graph::NewGraph)
    np = graph.np
    gconstr = graph.gconstr
    pkgs = graph.data.pkgs

    id(p0::Int) = pkgID(pkgs[p0], graph)

    for p0 = 1:np
        if !any(gconstr[p0])
            err_msg = "Unsatisfiable requirements detected for package $(id(p0)):\n"
            # err_msg *= sprint(showitem, bktrc, p)
            # err_msg *= """The intersection of the requirements is $(bktrc[p].versionreq).
            #               None of the available versions can satisfy this requirement."""
            throw(PkgError(err_msg))
        end
    end
    return true
end

"""
Propagates current constraints, determining new implicit constraints.
Throws an error in case impossible requirements are detected.
"""
function propagate_constraints!(graph::NewGraph)
    np = graph.np
    spp = graph.spp
    gadj = graph.gadj
    gmsk = graph.gmsk
    gconstr = graph.gconstr
    adjdict = graph.adjdict
    pkgs = graph.data.pkgs

    id(p0::Int) = pkgID(pkgs[p0], graph)

    # packages which are not allowed to be uninstalled
    staged = Set{Int}(p0 for p0 = 1:np if !gconstr[p0][end])

    while !isempty(staged)
        staged_next = Set{Int}()
        for p0 in staged
            gconstr0 = gconstr[p0]
            for (j1,p1) in enumerate(gadj[p0])
                msk = gmsk[p0][j1]
                # consider the sub-mask with only allowed versions of p0
                sub_msk = msk[:,gconstr0]
                # if an entire row of the sub-mask is false, that version of p1
                # is effectively forbidden
                # (this is just like calling `any` row-wise)
                added_constr1 = any!(BitVector(spp[p1]), sub_msk)
                # apply the new constraints, checking for contradictions
                # (keep the old ones for comparison)
                gconstr1 = gconstr[p1]
                old_gconstr1 = copy(gconstr1)
                gconstr1 .&= added_constr1
                if !any(gconstr1)
                    err_msg = "Unsatisfiable requirements detected for package $(id(p1)):\n"
                    # err_msg *= sprint(showitem, bktrc, p)
                    # err_msg *= """The intersection of the requirements is $(bktrc[p].versionreq).
                    #               None of the available versions can satisfy this requirement."""
                    throw(PkgError(err_msg))
                end
                # if the new constraints are more restrictive than the
                # previous ones, propagate them next
                gconstr1 ≠ old_gconstr1 && push!(staged_next, p1)
            end
        end
        staged = staged_next
    end
    return graph
end

"Enforce the uninstalled state on all packages that are not reachable from the required ones"
function disable_unreachable!(graph::NewGraph)
    np = graph.np
    spp = graph.spp
    gadj = graph.gadj
    gmsk = graph.gmsk
    gconstr = graph.gconstr
    adjdict = graph.adjdict
    pkgs = graph.data.pkgs

    # packages which are not allowed to be uninstalled
    staged = Set{Int}(p0 for p0 = 1:np if !gconstr[p0][end])
    seen = copy(staged)

    while !isempty(staged)
        staged_next = Set{Int}()
        for p0 in staged
            gconstr0idx = find(gconstr[p0][1:(end-1)])
            for (j1,p1) in enumerate(gadj[p0])
                all(gmsk[p0][j1][end,gconstr0idx]) && continue # the package is not required by any of the allowed versions of p0
                p1 ∈ seen || push!(staged_next, p1)
            end
        end
        union!(seen, staged_next)
        staged = staged_next
    end

    # Force uninstalled state for all unseen packages
    for p0 = 1:np
        p0 ∈ seen && continue
        gconstr0 = gconstr[p0]
        @assert gconstr0[end]
        fill!(gconstr0, false)
        gconstr0[end] = true
    end

    return graph
end

"""
Prune away fixed and unnecessary packages, and the
disallowed versions for the remaining packages.
"""
function prune_graph!(graph::NewGraph)
    np = graph.np
    spp = graph.spp
    gadj = graph.gadj
    gmsk = graph.gmsk
    gdir = graph.gdir
    gconstr = graph.gconstr
    adjdict = graph.adjdict
    req_inds = graph.req_inds
    fix_inds = graph.fix_inds
    data = graph.data
    pkgs = data.pkgs
    pdict = data.pdict
    pvers = data.pvers
    vdict = data.vdict
    pruned = data.pruned

    info("Simplifying")

    # We will remove all packages that only have one allowed state
    # (includes fixed packages and forbidden packages)
    pkg_mask = BitArray(count(gconstr[p0]) ≠ 1 for p0 = 1:np)
    new_np = count(pkg_mask)

    # a map that translates the new index ∈ 1:new_np into its
    # corresponding old index ∈ 1:np
    old_idx = find(pkg_mask)
    # the reverse of the above
    new_idx = Dict{Int,Int}()
    for new_p0 = 1:new_np
        new_idx[old_idx[new_p0]] = new_p0
    end

    # Update requirement indices
    new_req_inds = Set{Int}()
    for p0 in req_inds
        pkg_mask[p0] || continue
        push!(new_req_inds, new_idx[p0])
    end

    # Fixed packages will all be pruned
    new_fix_inds = Set{Int}()
    for p0 in fix_inds
        @assert !pkg_mask[p0]
    end

    # Record which packages we are going to prune
    for p0 in find(.~(pkg_mask))
        # Find the version
        s0 = findfirst(gconstr[p0])
        # We don't record fixed packages
        p0 ∈ fix_inds && (@assert s0 ≠ spp[p0]; continue)
        p0 ∈ req_inds && @assert s0 ≠ spp[p0]
        # We don't record packages that are not going to be installed
        s0 == spp[p0] && continue
        @assert !haskey(pruned, pkgs[p0])
        pruned[pkgs[p0]] = pvers[p0][s0]
    end

    # Update packages records
    new_pkgs = pkgs[pkg_mask]
    new_pdict = Dict(new_pkgs[new_p0]=>new_p0 for new_p0 = 1:new_np)

    # println("  old_pkgs = ", map(u->data.uuid_to_name[u], pkgs))
    # println("  new_pkgs = ", map(u->data.uuid_to_name[u], new_pkgs))

    # For each package (unless it's going to be pruned) we will remove all
    # versions that aren't allowed (but not the "uninstalled" state)
    function keep_vers(new_p0)
        p0 = old_idx[new_p0]
        return BitArray((v0 == spp[p0]) | gconstr[p0][v0] for v0 = 1:spp[p0])
    end
    vers_mask = [keep_vers(new_p0) for new_p0 = 1:new_np]

    # Update number of states per package
    new_spp = Int[count(vers_mask[new_p0]) for new_p0 = 1:new_np]

    # Update versions maps
    function compute_pvers(new_p0)
        p0 = old_idx[new_p0]
        pvers0 = pvers[p0]
        vmsk0 = vers_mask[new_p0]
        return pvers0[vmsk0[1:(end-1)]]
    end
    new_pvers = [compute_pvers(new_p0) for new_p0 = 1:new_np]
    new_vdict = [Dict(vn => v0 for (v0,vn) in enumerate(new_pvers[new_p0])) for new_p0 = 1:new_np]

    # The new constraints are all going to be `true`, except possibly
    # for the "uninstalled" state, which we copy over from the old
    function compute_gconstr(new_p0)
        p0 = old_idx[new_p0]
        new_gconstr0 = trues(new_spp[new_p0])
        new_gconstr0[end] = gconstr[p0][end]
        return new_gconstr0
    end
    new_gconstr = [compute_gconstr(new_p0) for new_p0 = 1:new_np]

    # Recreate the graph adjacency list, skipping some packages
    new_gadj = [Int[] for new_p0 = 1:new_np]
    new_adjdict = [Dict{Int,Int}() for new_p0 = 1:new_np]

    for new_p0 = 1:new_np, (j1,p1) in enumerate(gadj[old_idx[new_p0]])
        pkg_mask[p1] || continue
        new_p1 = new_idx[p1]

        new_j0 = get(new_adjdict[new_p1], new_p0, length(new_gadj[new_p0]) + 1)
        new_j1 = get(new_adjdict[new_p0], new_p1, length(new_gadj[new_p1]) + 1)

        @assert (new_j0 > length(new_gadj[new_p0]) && new_j1 > length(new_gadj[new_p1])) ||
                (new_j0 ≤ length(new_gadj[new_p0]) && new_j1 ≤ length(new_gadj[new_p1]))

        new_j0 > length(new_gadj[new_p0]) || continue
        push!(new_gadj[new_p0], new_p1)
        push!(new_gadj[new_p1], new_p0)
        new_j0 = length(new_gadj[new_p0])
        new_j1 = length(new_gadj[new_p1])

        new_adjdict[new_p1][new_p0] = new_j0
        new_adjdict[new_p0][new_p1] = new_j1
    end

    # Recompute gdir on the new adjacency list
    function compute_gdir(new_p0, new_j0)
        p0 = old_idx[new_p0]
        new_p1 = new_gadj[new_p0][new_j0]
        p1 = old_idx[new_p1]
        j0 = adjdict[p1][p0]
        return gdir[p0][j0]
    end
    new_gdir = [[compute_gdir(new_p0, new_j0) for new_j0 = 1:length(new_gadj[new_p0])] for new_p0 = 1:new_np]

    # Recompute compatibility masks on the new adjacency list, and filtering out some versions
    function compute_gmsk(new_p0, new_j0)
        p0 = old_idx[new_p0]
        new_p1 = new_gadj[new_p0][new_j0]
        p1 = old_idx[new_p1]
        j0 = adjdict[p1][p0]
        return gmsk[p0][j0][vers_mask[new_p1],vers_mask[new_p0]]
    end
    new_gmsk = [[compute_gmsk(new_p0, new_j0) for new_j0 = 1:length(new_gadj[new_p0])] for new_p0 = 1:new_np]

    # Done

    info("""
         PRUNING STATS:
           before: np = $np ⟨spp⟩ = $(mean(spp))
           after:  np = $new_np ⟨spp⟩ = $(mean(new_spp))
        """)

    # Replace old data with new
    data.pkgs = new_pkgs
    data.np = new_np
    data.spp = new_spp
    data.pdict = new_pdict
    data.pvers = new_pvers
    data.vdict = new_vdict
    # Notes:
    #   * uuid_to_name, reqs and fixed are unchanged
    #   * pruned was updated in-place

    # Replace old structures with new ones
    graph.gadj = new_gadj
    graph.gmsk = new_gmsk
    graph.gdir = new_gdir
    graph.gconstr = new_gconstr
    graph.adjdict = new_adjdict
    graph.req_inds = new_req_inds
    graph.fix_inds = new_fix_inds
    graph.spp = new_spp
    graph.np = new_np

    @assert check_consistency(graph)

    return graph
end

"""
Simplifies the graph by propagating constraints, disabling unreachable versions and
then pruning.
"""
function simplify_graph!(graph::NewGraph)
    propagate_constraints!(graph)
    disable_unreachable!(graph)
    prune_graph!(graph)
    return graph
end


# function check_fixed(reqs::Requires, fix::Dict{UUID,Fixed}, graph::NewGraph)
#     id(p) = pkgID(p, deps)
#     for (p1,f1) in fix
#         for p2 in keys(f1.requires)
#             if !(haskey(graph.data.pkgs, p2) || haskey(fix, p2))
#                 throw(PkgError("unknown package $(id(p1)) required by $(id(p2))"))
#             end
#         end
#         if !satisfies(p1, f1.version, reqs)
#             warn("$(id(p1)) is fixed at $(f1.version) conflicting with top-level requirement: $(reqs[p1])")
#         end
#         for (p2,f2) in fix
#             if !satisfies(p1, f1.version, f2.requires)
#                 warn("$(id(p1)) is fixed at $(f1.version) conflicting with requirement for $(id(p2)): $(f2.requires[p1])")
#             end
#         end
#     end
# end
#
# function propagate_fixed!(reqs::Requires, bktrc::ResolveBacktrace, fix::Dict{UUID,Fixed})
#     for (p,f) in fix
#         merge_requires!(reqs, f.requires)
#         for (rp,rvs) in f.requires
#             bktrc_rp = get!(bktrc, rp) do; ResolveBacktraceItem() end
#             push!(bktrc_rp, p=>bktrc[p], rvs)
#         end
#     end
#     for (p,f) in fix
#         delete!(reqs, p)
#     end
#     reqs
# end
#
# # Generate a reverse dependency graph (package names only)
# function gen_backdeps(deps::DepsGraph)
#     backdeps = Dict{UUID,Set{UUID}}()
#     for (p,depsp) in deps, (vn,vdep) in depsp, rp in keys(vdep)
#         s = get!(backdeps, rp) do; Set{UUID}() end
#         push!(s, p)
#     end
#     return backdeps
# end
#
# function dependencies(graph::NewGraph, fix::Dict = Dict{UUID,Fixed}(uuid_julia=>Fixed(VERSION)))
#     np = graph.np
#     spp = graph.spp
#     gadj = graph.gadj
#     gmsk = graph.gmsk
#     adjdict = graph.adjdict
#     pkgs = graph.data.pkgs
#     pdict = graph.data.pdict
#     vdict = graph.data.vdict
#
#     conflicts = Dict{UUID,Set{UUID}}()
#     vers_to_expunge = [falses(spp[p0]-1) for p0 = 1:np]
#     links_to_expunge = [Int[] for p0 = 1:np]
#     emptied = Int[]
#
#
#     for (fp,fx) in fix
#         delete!(deps, fp)
#         fp0 = pdict[fp]         # TODO: make sure that fix always appear in the graph?
#         fv0 = vdict[fx.version]
#
#         for (j1,p1) in gadj[fp0]
#             to_expunge = .~(gmsk[fp0][j1][1:(end-1),fv0]) # mask of incompatible versions of p1
#
#             if any(to_expunge)
#                 conflicts_p = get!(conflicts, pkgs[p1]) do; Set{UUID}() end
#                 push!(conflicts_p, fp)
#                 vers_to_expunge[p1] .|= to_expunge
#                 all(vers_to_expunge[p1]) && push(emptied, p1)
#             else
#                 push!(links_to_expunge[p1], adjdict[p1][fp0])
#                 push!(links_to_expunge[fp0], j1)
#             end
#             isempty(depsp) && push!(emptied, p)
#         end
#     end
#     # XXX ...
#
#     while !isempty(emptied)
#         deleted_pkgs = UUID[]
#         for p in emptied
#             delete!(deps, p)
#             push!(deleted_pkgs, p)
#         end
#         empty!(emptied)
#
#         for dp in deleted_pkgs
#             haskey(backdeps, dp) || continue
#             for p in backdeps[dp]
#                 haskey(deps, p) || continue
#                 depsp = deps[p]
#                 empty!(to_expunge)
#                 for (vn,vdep) in depsp
#                     haskey(vdep, dp) || continue
#                     conflicts_p = get!(conflicts, p) do; Set{UUID}() end
#                     union!(conflicts_p, conflicts[dp])
#                     push!(to_expunge, vn)
#                 end
#                 for vn in to_expunge
#                     delete!(depsp, vn)
#                 end
#                 isempty(depsp) && push!(emptied, p)
#             end
#         end
#     end
#     deps, conflicts
# end
#
# function check_requirements(reqs::Requires, deps::DepsGraph, fix::Dict{UUID,Fixed})
#     id(p) = pkgID(p, deps)
#     for (p,vs) in reqs
#         any(vn->(vn ∈ vs), keys(deps[p])) && continue
#         remaining_vs = VersionSpec()
#         err_msg = "fixed packages introduce conflicting requirements for $(id(p)): \n"
#         available_list = sort!(collect(keys(deps[p])))
#         for (p1,f1) in fix
#             f1r = f1.requires
#             haskey(f1r, p) || continue
#             err_msg *= "         $(id(p1)) requires versions $(f1r[p])"
#             if !any([vn in f1r[p] for vn in available_list])
#                 err_msg *= " [none of the available versions can satisfy this requirement]"
#             end
#             err_msg *= "\n"
#             remaining_vs = intersect(remaining_vs, f1r[p])
#         end
#         if isempty(remaining_vs)
#             err_msg *= "       the requirements are unsatisfiable because their intersection is empty"
#         else
#             err_msg *= "       available versions are $(join(available_list, ", ", " and "))"
#         end
#         throw(PkgError(err_msg))
#     end
# end
#
# # If there are explicitly required packages, dicards all versions outside
# # the allowed range.
# # It also propagates requirements: when all allowed versions of a required package
# # require some other package, this creates a new implicit requirement.
# # The propagation is tracked so that in case a contradiction is detected the error
# # message allows to determine the cause.
# # This is a pre-pruning step, so it also creates some structures which are later used by pruning
# function filter_versions(reqs::Requires, deps::DepsGraph, bktrc::ResolveBacktrace)
#     id(p) = pkgID(p, deps)
#     allowed = Dict{UUID,Dict{VersionNumber,Bool}}()
#     staged = copy(reqs)
#     while !isempty(staged)
#         staged_next = Requires()
#         for (p,vs) in staged
#             # Parse requirements and store allowed versions.
#             depsp = deps[p]
#             if !haskey(allowed, p)
#                 allowedp = Dict{VersionNumber,Bool}(vn=>true for vn in keys(depsp))
#                 allowed[p] = allowedp
#                 seen = false
#             else
#                 allowedp = allowed[p]
#                 oldallowedp = copy(allowedp)
#                 seen = true
#             end
#             for vn in keys(depsp)
#                 allowedp[vn] &= vn ∈ vs
#             end
#             @assert !isempty(allowedp)
#             if !any(values(allowedp))
#                 err_msg = "Unsatisfiable requirements detected for package $(id(p)):\n"
#                 err_msg *= sprint(showitem, bktrc, p)
#                 err_msg *= """The intersection of the requirements is $(bktrc[p].versionreq).
#                               None of the available versions can satisfy this requirement."""
#                 throw(PkgError(err_msg))
#             end
#
#             # If we've seen this package already and nothing has changed since
#             # the last time, we stop here.
#             seen && allowedp == oldallowedp && continue
#
#             # Propagate requirements:
#             # if all allowed versions of a required package require some other package,
#             # then compute the union of the allowed versions for that other package, and
#             # treat that as a new requirement.
#             # Start by filtering out the non-allowed versions
#             fdepsp = Dict{VersionNumber,Requires}(vn=>depsp[vn] for vn in keys(depsp) if allowedp[vn])
#             # Collect all required packages
#             isreq = Dict{UUID,Bool}(rp=>true for vdep in values(fdepsp) for rp in keys(vdep))
#             # Compute whether a required package appears in all requirements
#             for rp in keys(isreq)
#                 isreq[rp] = all(haskey(vdep, rp) for vdep in values(fdepsp))
#             end
#
#             # Create a list of candidates for new implicit requirements
#             staged_new = Set{UUID}()
#             for vdep in values(fdepsp), (rp,rvs) in vdep
#                 # Skip packages that may not be required
#                 isreq[rp] || continue
#                 # Compute the union of the version sets
#                 if haskey(staged_next, rp)
#                     snvs = staged_next[rp]
#                     union!(snvs, rvs)
#                 else
#                     snvs = copy(rvs)
#                     staged_next[rp] = snvs
#                 end
#                 push!(staged_new, rp)
#             end
#             for rp in staged_new
#                 @assert isreq[rp]
#                 srvs = staged_next[rp]
#                 bktrcp = get!(bktrc, rp) do; ResolveBacktraceItem(); end
#                 push!(bktrcp, p=>bktrc[p], srvs)
#                 if isa(bktrcp.versionreq, VersionSpec) && isempty(bktrcp.versionreq)
#                     err_msg = "Unsatisfiable requirements detected for package $(id(rp)):\n"
#                     err_msg *= sprint(showitem, bktrc, rp)
#                     err_msg *= "The intersection of the requirements is empty."
#                     throw(PkgError(err_msg))
#                 end
#             end
#         end
#         staged = staged_next
#     end
#
#     filtered_deps = DepsGraph(deps.uuid_to_name)
#     for (p,depsp) in deps
#         filtered_deps[p] = Dict{VersionNumber,Requires}()
#         allowedp = get(allowed, p) do; Dict{VersionNumber,Bool}() end
#         fdepsp = filtered_deps[p]
#         for (vn,vdep) in depsp
#             get(allowedp, vn, true) || continue
#             fdepsp[vn] = vdep
#         end
#     end
#
#     return filtered_deps, allowed
# end
#
# # Reduce the number of versions by creating equivalence classes, and retaining
# # only the highest version for each equivalence class.
# # Two versions are equivalent if:
# #   1) They appear together as dependecies of another package (i.e. for each
# #      dependency relation, they are both required or both not required)
# #   2) They have the same dependencies
# # Preliminarily calls filter_versions.
# function prune_versions(reqs::Requires, deps::DepsGraph, bktrc::ResolveBacktrace)
#     filtered_deps, allowed = filter_versions(reqs, deps, bktrc)
#     if !isempty(reqs)
#         filtered_deps = dependencies_subset(filtered_deps, Set{UUID}(keys(reqs)))
#     end
#
#     # To each version in each package, we associate a BitVector.
#     # It is going to hold a pattern such that all versions with
#     # the same pattern are equivalent.
#     vmask = Dict{UUID,Dict{VersionNumber,BitVector}}()
#
#     # For each package, we examine the dependencies of its versions
#     # and put together those which are equal.
#     # While we're at it, we also collect all dependencies into alldeps
#     alldeps = Dict{UUID,Set{VersionSpec}}()
#     for (p,fdepsp) in filtered_deps
#         # Extract unique dependencies lists (aka classes), thereby
#         # assigning an index to each class.
#         uniqdepssets = unique(values(fdepsp))
#
#         # Store all dependencies seen so far for later use
#         for r in uniqdepssets, (rp,rvs) in r
#             get!(alldeps, rp) do; Set{VersionSpec}() end
#             push!(alldeps[rp], rvs)
#         end
#
#         # If the package has just one version, it's uninteresting
#         length(deps[p]) == 1 && continue
#
#         # Grow the pattern by the number of classes
#         luds = length(uniqdepssets)
#         @assert !haskey(vmask, p)
#         vmask[p] = Dict{VersionNumber,BitVector}()
#         vmaskp = vmask[p]
#         for vn in keys(fdepsp)
#             vmaskp[vn] = falses(luds)
#         end
#         for (vn,vdep) in fdepsp
#             vmind = findfirst(equalto(vdep), uniqdepssets)
#             @assert vmind > 0
#             vm = vmaskp[vn]
#             vm[vmind] = true
#         end
#     end
#
#     # Produce dependency patterns.
#     for (p,vss) in alldeps, vs in vss
#         # packages with just one version, or dependencies
#         # which do not distiguish between versions, are not
#         # interesting
#         (length(deps[p]) == 1 || vs == VersionSpec()) && continue
#
#         # Store the dependency info in the patterns
#         @assert haskey(vmask, p)
#         for (vn,vm) in vmask[p]
#             push!(vm, vn in vs)
#         end
#     end
#
#     # At this point, the vmask patterns are computed. We divide them into
#     # classes so that we can keep just one version for each class.
#     pruned_vers = Dict{UUID,Vector{VersionNumber}}()
#     eq_classes = Dict{UUID,Dict{VersionNumber,Vector{VersionNumber}}}()
#     for (p,vmaskp) in vmask
#         vmask0_uniq = unique(values(vmaskp))
#         nc = length(vmask0_uniq)
#         classes = [VersionNumber[] for c0 = 1:nc]
#         for (vn,vm) in vmaskp
#             c0 = findfirst(equalto(vm), vmask0_uniq)
#             push!(classes[c0], vn)
#         end
#         map(sort!, classes)
#
#         # For each nonempty class, we store only the highest version)
#         pruned_vers[p] = VersionNumber[]
#         prunedp = pruned_vers[p]
#         eq_classes[p] = Dict{VersionNumber,Vector{VersionNumber}}()
#         eqclassp = eq_classes[p]
#         for cl in classes
#             isempty(cl) && continue
#             vtop = maximum(cl)
#             push!(prunedp, vtop)
#             @assert !haskey(eqclassp, vtop)
#             eqclassp[vtop] = cl
#         end
#         sort!(prunedp)
#     end
#     # Put non-allowed versions into eq_classes
#     for (p,allowedp) in allowed
#         haskey(eq_classes, p) || continue
#         eqclassp = eq_classes[p]
#         for (vn,a) in allowedp
#             a && continue
#             eqclassp[vn] = [vn]
#         end
#     end
#     # Put all remaining packages into eq_classes
#     for (p,depsp) in deps
#         haskey(eq_classes, p) && continue
#         eq_classes[p] = Dict{VersionNumber,Vector{VersionNumber}}()
#         eqclassp = eq_classes[p]
#         for vn in keys(depsp)
#             eqclassp[vn] = [vn]
#         end
#     end
#
#
#     # Recompute deps. We could simplify them, but it's not worth it
#     new_deps = DepsGraph(deps.uuid_to_name)
#
#     for (p,depsp) in filtered_deps
#         @assert !haskey(new_deps, p)
#         if !haskey(pruned_vers, p)
#             new_deps[p] = depsp
#             continue
#         end
#         new_deps[p] = Dict{VersionNumber,Requires}()
#         pruned_versp = pruned_vers[p]
#         for (vn,vdep) in depsp
#             vn ∈ pruned_versp || continue
#             new_deps[p][vn] = vdep
#         end
#     end
#
#     #println("pruning stats:")
#     #numvers = 0
#     #numdeps = 0
#     #for (p,d) in deps, (vn,vdep) in d
#     #    numvers += 1
#     #    for r in vdep
#     #        numdeps += 1
#     #    end
#     #end
#     #numnewvers = 0
#     #numnewdeps = 0
#     #for (p,d) in new_deps, (vn,vdep) in d
#     #    numnewvers += 1
#     #    for r in vdep
#     #        numnewdeps += 1
#     #    end
#     #end
#     #println("  before: vers=$numvers deps=$numdeps")
#     #println("  after: vers=$numnewvers deps=$numnewdeps")
#     #println()
#
#     return new_deps, eq_classes
# end
# prune_versions(deps::DepsGraph) =
#     prune_versions(Requires(), deps, ResolveBacktrace(deps.uuid_to_name))
#
# # Build a graph restricted to a subset of the packages
# function subdeps(deps::DepsGraph, pkgs::Set{UUID})
#     sub_deps = DepsGraph(deps.uuid_to_name)
#     for p in pkgs
#         haskey(sub_deps, p) || (sub_deps[p] = Dict{VersionNumber,Requires}())
#         sub_depsp = sub_deps[p]
#         for (vn,vdep) in deps[p]
#             sub_depsp[vn] = vdep
#         end
#     end
#     return sub_deps
# end
#
# # Build a subgraph incuding only the (direct and indirect) dependencies
# # of a given package set
# function dependencies_subset(deps::DepsGraph, pkgs::Set{UUID})
#     staged::Set{UUID} = filter(p->p ∈ keys(deps), pkgs)
#     allpkgs = copy(staged)
#     while !isempty(staged)
#         staged_next = Set{UUID}()
#         for p in staged, vdep in values(get(deps, p, Dict{VersionNumber,Requires}())), rp in keys(vdep)
#             rp ∉ allpkgs && rp ≠ uuid_julia && push!(staged_next, rp)
#         end
#         union!(allpkgs, staged_next)
#         staged = staged_next
#     end
#
#     return subdeps(deps, allpkgs)
# end
#
# # Build a subgraph incuding only the (direct and indirect) dependencies and dependants
# # of a given package set
# function undirected_dependencies_subset(deps::DepsGraph, pkgs::Set{UUID})
#     graph = Dict{UUID,Set{UUID}}()
#
#     for (p,d) in deps
#         haskey(graph, p) || (graph[p] = Set{UUID}())
#         for vdep in values(d), rp in keys(vdep)
#             push!(graph[p], rp)
#             haskey(graph, rp) || (graph[rp] = Set{UUID}())
#             push!(graph[rp], p)
#         end
#     end
#
#     staged = pkgs
#     allpkgs = copy(pkgs)
#     while !isempty(staged)
#         staged_next = Set{UUID}()
#         for p in staged, rp in graph[p]
#             rp ∉ allpkgs && push!(staged_next, rp)
#         end
#         union!(allpkgs, staged_next)
#         staged = staged_next
#     end
#
#     return subdeps(deps, allpkgs)
# end
#
# function prune_dependencies(reqs::Requires, deps::DepsGraph,
#                             bktrc::ResolveBacktrace = init_resolve_backtrace(deps.uuid_to_name, reqs))
#     deps, _ = prune_versions(reqs, deps, bktrc)
#     return deps
# end

end # module
