# Theorem 5.1: multisets of powers of one odd prime.
include("common.jl")
cp(p) = prod(1 - big(1.0)/big(p)^d for d in 1:300)
# (1) p = 3, 5: the F allowed by inequality (5.4); tail by phi(F) >= sqrt(F/2)
for p in (3, 5)
    allowed = Int[]
    for F in 3:5000
        ph = totient(F)
        lhs = max(ph * log(big(p - 1)), log(cp(p)) + ph * log(big(p))) - log(big(F))
        rhs = log2(big(p) / (p - 1)) * log(big(p^2 - 1) * F / 2)
        lhs < rhs && push!(allowed, F)
    end
    tailstart = maximum(F for F in 3:5000 if log(cp(p)) + sqrt(big(F) / 2) * log(big(p)) - log(big(F)) <=
                        log2(big(p) / (p - 1)) * log(big(p^2 - 1) * F / 2))
    println("p=$p allowed F=$allowed ; sqrt-bound suffices beyond F=$tailstart")
    for F in vcat([2], allowed)
        kmax = floor(Int, log2((p^2 - 1) * F / 2))
        divs = sort([d for d in divisors(F) if d < F], rev = true)
        out = Vector{Vector{Int}}(); parts(F, divs, F, Int[], out)
        n = 0
        for S in out
            (length(S) < 2 || length(S) > kmax) && continue
            n += 1
            if (big(p)^F - 1) % prod(big(p)^f - 1 for f in S) == 0
                println("   solution p=$p F=$F S=$S M=", (big(p)^F - 1) ÷ prod(big(p)^f - 1 for f in S))
            end
        end
        println("   p=$p F=$F candidates=$n")
    end
end
# (2) p >= 7: g(F) > 0 for 3 <= F <= 7 and h(F) > 0, increasing, for F >= 8
g(F) = 1.7917 * (totient(F) - 0.525) - 1.2405 * log(F)
h(F) = 1.7917 * (sqrt(F / 2) - 0.525) - 1.2405 * log(F)
println("g(3..7) = ", [round(g(F), digits = 3) for F in 3:7], "  h(8) = ", round(h(8), digits = 4))
@assert all(g(F) > 0.42 for F in 3:7) && h(8) > 0.06
@assert all(h(F + 1) > h(F) for F in 4:100000)
@assert all(1 / ((p - 1) * log(2)) <= 0.2405 && log(p) <= 1.09 * log(p - 1) for p in 7:100000)
# (3) brute force: all odd p < 200, all S with F <= 16 (Lehmer) and companion
for p in 3:2:199
    isprime_mr(p) || continue
    for F in 2:16
        out = Vector{Vector{Int}}(); parts(F, collect(F:-1:1), F, Int[], out)
        for S in out
            length(S) < 2 && continue
            P = prod(big(p)^f - 1 for f in S)
            (big(p)^F - 1) % P == 0 && println("   brute Lehmer p=$p S=$S")
            (big(p)^F + 1) % P == 0 && println("   brute COMPANION p=$p S=$S")
        end
    end
end
println("done")
