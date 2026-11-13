from math import prod, log, log2
from sympy import totient, divisors, primerange
def parts(n, divs, maxpart):
    # multisets (nonincreasing) of elements of divs summing to n
    if n==0: yield []; return
    for d in divs:
        if d<=maxpart and d<=n:
            for r in parts(n-d, divs, d): yield [d]+r
# binary, t in {0,1}
sols=[]
for F in [2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,22,24,30]:
    for t in (0,1):
        divs=sorted([d for d in divisors(F) if 2<=d<F],reverse=True)
        for S in parts(F-t,divs,F):
            if len(S)+t<2: continue
            if (2**F-1)%prod(2**f-1 for f in S)==0: sols.append((F,t,tuple(S)))
print('binary t<=1:',sols)
# odd p single characteristic: all f | F, sum = F, k>=2
for p in primerange(3,200):
    # bound F: phi(F)*log p + log 0.56 - log F < k*log(p/(p-1)) with k <= log2(p^2-1)+log2 F
    Fmax=2
    for F in range(3,3000):
        k=log2(p*p-1)+log2(F)
        if totient(F)*log(p)+log(0.56)-log(F) < k*log(p/(p-1)): Fmax=F
    found=[]
    for F in range(2,Fmax+1):
        divs=sorted([d for d in divisors(F) if d<F],reverse=True)
        for S in parts(F,divs,F):
            if len(S)<2: continue
            if (p**F-1)%prod(p**f-1 for f in S)==0: found.append((F,tuple(S)))
    if found or p<20: print(p,Fmax,found)
