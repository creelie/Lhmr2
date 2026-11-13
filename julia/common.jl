# Shared helpers: deterministic Miller-Rabin (correct below 3.3e24), prime powers, totient.
const SP = (2,3,5,7,11,13,17,19,23,29,31,37,41)
function isprime_mr(n::Integer)
    n < 2 && return false
    for p in SP
        n % p == 0 && return n == p
    end
    d = n - 1; s = 0
    while iseven(d); d >>= 1; s += 1; end
    N = big(n)
    for a in SP
        x = powermod(big(a), big(d), N)
        (x == 1 || x == N - 1) && continue
        ok = false
        for _ in 1:s-1
            x = mod(x * x, N)
            if x == N - 1; ok = true; break; end
        end
        ok || return false
    end
    return true
end
# returns (p,f) if n = p^f with p prime, f >= 1, else (0,0)
function primepower(n::Integer)
    n < 2 && return (0, 0)
    isprime_mr(n) && return (n, 1)
    for e in 2:64
        r = iroot(big(n), e)
        r < 2 && break
        r^e == n && isprime_mr(r) && return (Int128(r), e)
    end
    return (0, 0)
end
function iroot(n::BigInt, e::Int)
    n < 2 && return n
    lo = big(1); hi = big(2)^(div(ndigits(n, base=2), e) + 1)
    while lo < hi
        mid = (lo + hi + 1) >> 1
        if mid^e <= n; lo = mid; else hi = mid - 1; end
    end
    return lo
end
function totient(n::Integer)
    r = n; m = n; p = 2
    while p * p <= m
        if m % p == 0
            while m % p == 0; m ÷= p; end
            r -= r ÷ p
        end
        p += 1
    end
    m > 1 && (r -= r ÷ m)
    return r
end
divisors(n) = [d for d in 1:n if n % d == 0]
# nonincreasing multisets of elements of divs (descending) with sum n
function parts(n, divs, maxpart, acc, out)
    if n == 0; push!(out, copy(acc)); return; end
    for d in divs
        if d <= maxpart && d <= n
            push!(acc, d); parts(n - d, divs, d, acc, out); pop!(acc)
        end
    end
end
