# verify_c5.jl -- a third check of the drawings, colourings and finite reduction, in Julia.
#
#   julia verify_c5.jl ../data
#
# Reads witnesses16.txt, cands17.txt and wits16.txt. Checks Lemma 2.2 (26 and 36 dihedral classes),
# Lemma 2.1 by enumeration, and for each of the 36 witnesses: layers = edge set, plane straight-line
# drawings with exact Int arithmetic, proper 8-colouring.

const DIR = length(ARGS) > 0 ? ARGS[1] : joinpath(@__DIR__, "..", "data")

syms(w) = [begin x = circshift(w, -r); f ? reverse(x) : x end for r in 0:4 for f in (false, true)]
canon(w) = minimum(syms(w))
s_of(w) = maximum(w[i] + w[mod1(i + 1, 5)] for i in 1:5)
bags(w) = vcat([fill(i, w[i]) for i in 1:5]...)
function edgeset(w)
    b = bags(w); n = length(b)
    Set((u, v) for u in 0:n-1 for v in u+1:n-1 if mod(b[u+1] - b[v+1], 5) in (0, 1, 4))
end
readvecs(f) = [parse.(Int, split(l)) for l in eachline(joinpath(DIR, f)) if !isempty(strip(l)) && l[1] != '#']

orient(a, b, c) = (b[1] - a[1]) * (c[2] - a[2]) - (b[2] - a[2]) * (c[1] - a[1])
onseg(a, b, p) = orient(a, b, p) == 0 && min(a[1], b[1]) <= p[1] <= max(a[1], b[1]) && min(a[2], b[2]) <= p[2] <= max(a[2], b[2])
function meet(a, b, c, d)
    d1, d2, d3, d4 = sign(orient(c, d, a)), sign(orient(c, d, b)), sign(orient(a, b, c)), sign(orient(a, b, d))
    (d1 * d2 < 0 && d3 * d4 < 0) || onseg(c, d, a) || onseg(c, d, b) || onseg(a, b, c) || onseg(a, b, d)
end
function plane(n, E, P)
    length(unique(P)) == n || return false
    for (u, v) in E, x in 0:n-1
        x != u && x != v && onseg(P[u+1], P[v+1], P[x+1]) && return false
    end
    for i in 1:length(E), j in i+1:length(E)
        (a, b), (c, d) = E[i], E[j]
        length(Set((a, b, c, d))) == 4 && meet(P[a+1], P[b+1], P[c+1], P[d+1]) && return false
    end
    true
end

function main()
    ok = true
    check(c, msg) = (println(c ? "ok   " : "FAIL ", msg); ok &= c)
    c17 = readvecs("cands17.txt"); c16 = readvecs("wits16.txt")
    allw = [collect(t) for t in Iterators.product(ntuple(_ -> 1:7, 5)...) if s_of(collect(t)) <= 8]
    k17 = Set(canon(w) for w in allw if sum(w) == 17); k16 = Set(canon(w) for w in allw if sum(w) == 16)
    check(length(k17) == 26 && k17 == Set(canon.(c17)), "26 classes with n = 17")
    check(length(k16) == 36 && k16 == Set(canon.(c16)), "36 classes with n = 16")
    le(a, b) = all(a .<= b)
    check(all(any(le(c, g) for c in c17 for g in syms(w)) for w in allw if sum(w) >= 17), "Lemma 2.1(a)")
    check(all(any(le(g, c) for c in c16 for g in syms(w)) for w in allw if sum(w) <= 16), "Lemma 2.1(b)")

    lines = [l for l in eachline(joinpath(DIR, "witnesses16.txt")) if !startswith(l, "#")]
    k = parse(Int, lines[1]); i = 2; bad = 0
    for _ in 1:k
        w = parse.(Int, split(lines[i])[2:end]); i += 1
        n = sum(w); E = edgeset(w); covered = Set{Tuple{Int,Int}}(); good = true
        for j in 1:2
            m = parse(Int, split(lines[i])[3]); i += 1
            L = [Tuple(parse.(Int, split(lines[i+t]))) for t in 0:m-1]; i += m
            np = parse(Int, split(lines[i])[3]); i += 1
            P = [Tuple(parse.(Int, split(lines[i+t]))) for t in 0:np-1]; i += np
            good &= all(e in E for e in L) && plane(n, L, P)
            union!(covered, L)
        end
        col = parse.(Int, split(lines[i])[2:end]); i += 1
        good &= covered == E && length(col) == n && all(0 .<= col .<= 7) && all(col[u+1] != col[v+1] for (u, v) in E)
        bad += !good
    end
    check(k == 36 && bad == 0, "36 witnesses: layers cover the edges, plane drawings, proper 8-colourings")
    println(ok ? "ALL CHECKS PASSED" : "SOME CHECKS FAILED")
    exit(ok ? 0 : 1)
end

main()
