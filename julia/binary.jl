# Theorem 4.4/4.5/4.7: multisets of powers of two.
include("common.jl")
const c0 = prod(1 - big(2.0)^(-d) for d in 1:400)
const C2 = prod(1 / (1 - big(2.0)^(-v)) for v in 2:400)
function Eset(t; Fmax = 2000)
    E = Int[]
    for F in 3:Fmax
        lhs = log2(c0) + totient(F) - log2(big(F))
        rhs = t + (1 + log(big(F)) / log(big(3))) * log2(C2)
        lhs <= rhs && push!(E, F)
    end
    return E
end
# tail: phi(F) >= sqrt(F/2) excludes every F >= 2000 for t <= 12
function tail_ok(t)
    for F in 2000:200000
        lhs = log2(c0) + sqrt(big(F) / 2) - log2(big(F))
        rhs = t + (1 + log(big(F)) / log(big(3))) * log2(C2)
        lhs <= rhs && return false
    end
    return true   # the difference is increasing beyond this range
end
total = 0
sols = Tuple{Int,Vector{Int}}[]
for t in 0:12
    E = Eset(t); @assert tail_ok(t)
    cnt = 0
    for F in E
        F - t < 0 && continue
        divs = sort([d for d in divisors(F) if 2 <= d < F], rev = true)
        out = Vector{Vector{Int}}()
        parts(F - t, divs, F, Int[], out)
        for S in out
            isempty(S) && continue
            t + length(S) < 2 && continue
            cnt += 1
            if (big(2)^F - 1) % prod(big(2)^f - 1 for f in S) == 0
                push!(sols, (t, S))
            end
        end
    end
    global total += cnt
    println("t=$t maxE=$(maximum(E)) |E|=$(length(E)) candidates=$cnt solutions=",
            [S for (tt, S) in sols if tt == t])
end
println("nontrivial Lehmer multisets of powers of 2 with t<=12: ", length(sols))
@assert length(sols) == 48
# companion: brute force over S with entries in 2..8, |S|<=6, t<=30 against Theorem 4.7
bad = 0
for t in 0:30, F in t+2:t+30
    divs = collect(8:-1:2)
    out = Vector{Vector{Int}}(); parts(F - t, divs, 8, Int[], out)
    for S in out
        isempty(S) && continue
        length(S) > 8 && continue
        t + length(S) < 2 && continue
        holds = (big(2)^F + 1) % prod(big(2)^f - 1 for f in S) == 0
        c = count(==(2), S)
        pred = all(==(2), S) && isodd(t) && (t + 2c) % 3^(c - 1) == 0
        holds != pred && (global bad += 1; println("MISMATCH t=$t S=$S"))
    end
end
println("companion criterion mismatches: ", bad)
# Lehmer {2^(t),4^(c)} criterion (Prop 4.6b)
for t in 1:60, c in 1:8
    F = t + 2c
    @assert ((big(2)^F - 1) % big(3)^c == 0) == (iseven(t) && F % 3^(c - 1) == 0)
end
println("Proposition 4.6(b) verified for t<=60, c<=8")
