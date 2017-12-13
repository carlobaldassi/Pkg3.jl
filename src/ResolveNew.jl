# This file is a part of Julia. License is MIT: https://julialang.org/license

module ResolveNew

include(joinpath("resolve", "VersionWeights.jl"))
include(joinpath("resolve", "MaxSumNew.jl"))

using ..Types
using .MaxSum
import ..Types: uuid_julia

export resolve, sanity_check

# Use the max-sum algorithm to resolve packages dependencies
function resolve(reqs::Requires, graph::NewGraph)
    id(p) = pkgID(p, graph)

    # attempt trivial solution first
    ok, sol = greedysolver(reqs, graph)

    ok && @goto solved

    # trivial solution failed, use maxsum solver
    msgs = Messages(graph, reqs)

    try
        sol = maxsum(graph, msgs)
    catch err
        isa(err, UnsatError) || rethrow(err)
        p = graph.data.pkgs[err.info]
        # TODO: build tools to analyze the problem, and suggest to use them here.
        msg =
            """
            resolve is unable to satisfy package requirements.
              The problem was detected when trying to find a feasible version
              for package $(id(p)).
              However, this only means that package $(id(p)) is involved in an
              unsatisfiable or difficult dependency relation, and the root of
              the problem may be elsewhere.
            """
        if msgs.num_nondecimated != graph.np
            msg *= """
                     (you may try increasing the value of the JULIA_PKGRESOLVE_ACCURACY
                      environment variable)
                   """
        end
        ## info("ERROR MESSAGE:\n" * msg)
        throw(PkgError(msg))
    end

    # verify solution (debug code) and enforce its optimality
    @assert verify_solution(sol, reqs, graph)
    enforce_optimality!(sol, reqs, graph)

    @label solved

    # return the solution as a Dict mapping UUID => VersionNumber
    return compute_output_dict(sol, graph)
end

# Scan dependencies for (explicit or implicit) contradictions
# function sanity_check(deps::DepsGraph, pkgs::Set{UUID} = Set{UUID}())
#     id(p) = pkgID(p, deps)
#
#     isempty(pkgs) || (deps = Query.undirected_dependencies_subset(deps, pkgs))
#
#     deps, eq_classes = Query.prune_versions(deps)
#
#     ndeps = Dict{UUID,Dict{VersionNumber,Int}}()
#
#     for (p,depsp) in deps
#         ndeps[p] = ndepsp = Dict{VersionNumber,Int}()
#         for (vn,vdep) in depsp
#             ndepsp[vn] = length(vdep)
#         end
#     end
#
#     vers = [(p,vn) for (p,depsp) in deps for vn in keys(depsp)]
#     sort!(vers, by=pvn->(-ndeps[pvn[1]][pvn[2]]))
#
#     nv = length(vers)
#
#     svdict = Dict{Tuple{UUID,VersionNumber},Int}(vers[i][1:2]=>i for i = 1:nv)
#
#     checked = falses(nv)
#
#     problematic = Tuple{String,VersionNumber,String}[]
#     i = 1
#     for (p,vn) in vers
#         ndeps[p][vn] == 0 && break
#         checked[i] && (i += 1; continue)
#
#         fixed = Dict{UUID,Fixed}(p=>Fixed(vn, deps[p][vn]), uuid_julia=>Fixed(VERSION))
#         sub_reqs = Requires()
#         bktrc = Query.init_resolve_backtrace(deps.uuid_to_name, sub_reqs, fixed)
#         Query.propagate_fixed!(sub_reqs, bktrc, fixed)
#         sub_deps = Query.dependencies_subset(deps, Set{UUID}([p]))
#         sub_deps, conflicts = Query.dependencies(sub_deps, fixed)
#
#         try
#             for rp in keys(sub_reqs)
#                 haskey(sub_deps, rp) && continue
#                 if uuid_julia in conflicts[rp]
#                     throw(PkgError("$(id(rp)) can't be installed because it has no versions that support $VERSION " *
#                        "of julia. You may need to update METADATA by running `Pkg.update()`"))
#                 else
#                     sconflicts = join(map(id, conflicts[rp]), ", ", " and ")
#                     throw(PkgError("$(id(rp)) requirements can't be satisfied because " *
#                         "of the following fixed packages: $sconflicts"))
#                 end
#             end
#             Query.check_requirements(sub_reqs, sub_deps, fixed)
#             sub_deps = Query.prune_dependencies(sub_reqs, sub_deps, bktrc)
#         catch err
#             isa(err, PkgError) || rethrow(err)
#             ## info("ERROR MESSAGE:\n" * err.msg)
#             for vneq in eq_classes[p][vn]
#                 push!(problematic, (id(p), vneq, ""))
#             end
#             i += 1
#             continue
#         end
#         interface = Interface(sub_reqs, sub_deps)
#
#         red_pkgs = interface.pkgs
#         red_np = interface.np
#         red_spp = interface.spp
#         red_pvers = interface.pvers
#
#         ok, sol = greedysolver(interface)
#
#         if !ok
#             try
#                 graph = Graph(interface)
#                 msgs = Messages(interface, graph)
#                 sol = maxsum(graph, msgs)
#                 ok = verify_solution(sol, interface)
#                 @assert ok
#             catch err
#                 isa(err, UnsatError) || rethrow(err)
#                 pp = red_pkgs[err.info]
#                 for vneq in eq_classes[p][vn]
#                     push!(problematic, (id(p), vneq, pp))
#                 end
#             end
#         end
#         if ok
#             for p0 = 1:red_np
#                 s0 = sol[p0]
#                 if s0 != red_spp[p0]
#                     j = svdict[(red_pkgs[p0], red_pvers[p0][s0])]
#                     checked[j] = true
#                 end
#             end
#             checked[i] = true
#         end
#         i += 1
#     end
#
#     return sort!(problematic)
# end


# The output format is a Dict which associates a VersionNumber to each installed package name
function compute_output_dict(sol::Vector{Int}, graph::NewGraph)
    pkgs = graph.data.pkgs
    np = graph.np
    pvers = graph.data.pvers
    spp = graph.spp

    want = Dict{UUID,VersionNumber}()
    for p0 = 1:np
        p = pkgs[p0]
        s0 = sol[p0]
        s0 == spp[p0] && continue
        vn = pvers[p0][s0]
        want[p] = vn
    end

    return want
end

# Produce a trivial solution: try to maximize each version;
# bail out as soon as some non-trivial requirements are detected.
function greedysolver(reqs::Requires, graph::NewGraph)
    spp = graph.spp
    gadj = graph.gadj
    gmsk = graph.gmsk
    gdir = graph.gdir
    pdict = graph.data.pdict
    pvers = graph.data.pvers
    np = graph.np

    # initialize solution: all uninstalled
    sol = [spp[p0] for p0 = 1:np]

    # set up required packages to their highest allowed versions
    for (rp,rvs) in reqs
        rp0 = pdict[rp]
        # look for the highest version which satisfies the requirements
        rv0 = spp[rp0] - 1
        while rv0 > 0
            rvn = pvers[rp0][rv0]
            rvn ∈ rvs && break
            rv0 -= 1
        end
        @assert rv0 > 0
        sol[rp0] = rv0
    end

    # we start from required packages and explore the graph
    # following dependencies
    staged = Set{Int}(pdict[rp] for rp in keys(reqs))
    seen = copy(staged)

    while !isempty(staged)
        staged_next = Set{Int}()
        for p0 in staged
            s0 = sol[p0]
            @assert s0 < spp[p0]

            # scan dependencies
            for (j1,p1) in enumerate(gadj[p0])
                msk = gmsk[p0][j1]
                msk[end,s0] && continue # p1 is not required by p0's current version

                # look for the highest version which satisfies the requirements
                v1 = spp[p1] - 1
                while v1 > 0
                    msk[v1,s0] && break
                    v1 -= 1
                end
                # if we found a version, and the package was uninstalled
                # or the same version was already selected, we're ok;
                # otherwise we can't be sure what the optimal configuration is
                # and we bail out
                if v1 > 0 && (sol[p1] == spp[p1] || sol[p1] == v1)
                    sol[p1] = v1
                else
                    return (false, Int[])
                end

                p1 ∈ seen || push!(staged_next, p1)
            end
        end
        union!(seen, staged_next)
        staged = staged_next
    end

    @assert verify_solution(sol, reqs, graph)

    return true, sol
end

# verifies that the solution fulfills all hard constraints
# (requirements and dependencies)
function verify_solution(sol::Vector{Int}, reqs::Requires, graph::NewGraph)
    np = graph.np
    spp = graph.spp
    gadj = graph.gadj
    gmsk = graph.gmsk
    pdict = graph.data.pdict
    pvers = graph.data.pvers

    # verify requirements
    for (p,vs) in reqs
        p0 = pdict[p]
        sol[p0] ≠ spp[p0] || return false # TODO: print debug info
        vn = pvers[p0][sol[p0]]
        vn ∈ vs || return false # TODO: print debug info
    end

    # verify dependencies
    for p0 = 1:np
        s0 = sol[p0]
        for (j1,p1) in enumerate(gadj[p0])
            msk = gmsk[p0][j1]
            s1 = sol[p1]
            msk[s1,s0] || return false # TODO: print debug info
        end
    end
    return true
end

# Push the given solution to a local optimium if needed
function enforce_optimality!(sol::Vector{Int}, reqs::Requires, graph::NewGraph)
    np = graph.np

    spp = graph.spp
    gadj = graph.gadj
    gmsk = graph.gmsk
    gdir = graph.gdir
    pkgs = graph.data.pkgs
    pdict = graph.data.pdict
    pvers = graph.data.pvers

    restart = true
    while restart
        restart = false
        for p0 = 1:np
            s0 = sol[p0]
            s0 == spp[p0] && continue # the package is not installed,

            # check if bumping to the higher version would violate a requirement
            p = pkgs[p0]
            if haskey(reqs, p)
                s0 == spp[p0] - 1 && continue # can't uninstall!
                vs = reqs[p]
                vn = pvers[p0][s0+1]
                vn ∈ vs || continue
            end

            # check if bumping to the higher version would violate a constraint
            viol = false
            for (j1,p1) in enumerate(gadj[p0])
                s1 = sol[p1]
                msk = gmsk[p0][j1]
                if !msk[s1, s0+1]
                    viol = true
                    break
                end
            end
            viol && continue

            # So the solution is non-optimal: we bump it manually
            sol[p0] += 1
            restart = true
        end
    end

    # Finally uninstall unneeded packages:
    # start from the required ones and keep only
    # the packages reachable from them along the graph
    uninst = trues(np)
    staged = Set{Int}(pdict[rp] for rp in keys(reqs))
    seen = copy(staged)

    while !isempty(staged)
        staged_next = Set{Int}()
        for p0 in staged
            s0 = sol[p0]
            @assert s0 < spp[p0]
            uninst[p0] = false
            for (j1,p1) in enumerate(gadj[p0])
                sol[p1] < spp[p1] || continue
                gdir[p0][j1] ∈ (Types.BACKWARDS, Types.NONE) && continue
                p1 ∈ seen || push!(staged_next, p1)
            end
        end
        union!(seen, staged_next)
        staged = staged_next
    end

    for p0 in find(uninst)
        sol[p0] = spp[p0]
    end

    @assert verify_solution(sol, reqs, graph)
end

end # module
