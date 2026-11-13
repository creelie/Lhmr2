# Independent traversal of the search tree of Section 3.2 (modes Z, U, Q, G, E).
include("common.jl")
const MODE = Symbol(ARGS[1]); const EPS = parse(Int, ARGS[2]); const K = parse(Int, ARGS[3])
const LIMIT = big(2)^62
nodes = 0; terms = 0; sols = Vector{Tuple{Int,Vector{BigInt}}}(); skipped = 0
function ok_mode(seq, q, p, f)
    same = count(x -> x[2] == p, seq)
    MODE == :U && return true
    MODE == :Z && return f == 1 && (isempty(seq) || q > seq[end][1])
    if MODE == :Q
        f == 1 && return all(x -> !(x[2] == p && x[3] != 1), seq) && same < 2
        return f == 2 && same == 0
    elseif MODE == :G
        f == 1 && return p % 4 == 1 && same < 2
        return f == 2 && p % 4 == 3 && same == 0
    else # :E
        f == 1 && return (p == 3 ? same == 0 : (p % 3 == 1 && same < 2))
        return f == 2 && p % 3 == 2 && same == 0
    end
end
function compatible(seq, q, p, f, M)
    (isodd(q) && q >= 3) || return false
    !isempty(seq) && q < seq[end][1] && return false
    M % p == 0 && return false
    for (v, pv, _) in seq
        (q - 1) % pv == 0 && return false
        (v - 1) % p == 0 && return false
    end
    return ok_mode(seq, q, p, f)
end
reach(A, B, M, q, m) = EPS < 0 ? A * q^m > M * B * (q - 1)^m : A * q^m + 1 >= M * B * (q - 1)^m
function rec(seq, A, B, M)
    global nodes += 1
    j = length(seq); m = K - j
    C = M * B - A
    C <= 0 && return
    lo = max(div(M * B, C) + 1, isempty(seq) ? big(3) : seq[end][1], big(3))
    if lo >= LIMIT
        reach(A, B, M, lo, m) && (global skipped += 1)
        return
    end
    reach(A, B, M, lo, m) || return
    hi = lo
    while reach(A, B, M, 2hi, m); hi *= 2; end
    a, b = hi, 2hi
    while b - a > 1
        c = (a + b) >> 1
        reach(A, B, M, c, m) ? (a = c) : (b = c)
    end
    hi = a
    m == 2 && (global terms += 1)
    q = isodd(lo) ? lo : lo + 1
    while q <= hi
        p, f = primepower(q)
        if p != 0 && compatible(seq, q, p, f, M)
            if m == 2
                A2 = A * q; B2 = M * B * (q - 1); D = B2 - A2
                if D > 0 && (B2 + EPS) % D == 0
                    x = (B2 + EPS) ÷ D
                    px, fx = primepower(x)
                    if px != 0 && compatible(vcat(seq, [(q, p, f)]), x, px, fx, M)
                        push!(sols, (M, vcat([s[1] for s in seq], [q, x])))
                    end
                end
            else
                rec(vcat(seq, [(q, p, f)]), A * q, B * (q - 1), M)
            end
        end
        q += 2
    end
end
Mmax = floor(Int, 1.5^K) + 1
t0 = time()
for M in 2:Mmax
    rec(Tuple{BigInt,BigInt,Int}[], big(1), big(1), M)
end
println("mode=$MODE eps=$EPS K=$K nodes=$nodes terminal=$terms skipped=$skipped time=$(round(time()-t0,digits=1))s")
for (M, s) in sols; println("  SOL M=$M : ", join(s, " ")); end
