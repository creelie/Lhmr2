include("common.jl")
const c0 = prod(1 - big(1.0)/big(2)^d for d in 1:400)
const C2 = prod(1 / (1 - big(1.0)/big(2)^v) for v in 2:400)
for t in 0:12
    E = [F for F in 3:2000 if log2(c0) + totient(F) - log2(big(F)) <= t + (1 + log(big(F)) / log(big(3))) * log2(C2)]
    println(t, " ", join(E, ","))
end
