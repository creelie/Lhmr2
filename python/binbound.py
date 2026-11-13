from math import log, log2, sqrt
from sympy import totient
C=1.0
for v in range(2,200): C/= (1-2.0**-v)
c0=1.0
for d in range(1,200): c0*=(1-2.0**-d)
print('C',C,'c0',c0)
bad=[]
for F in range(2,5000):
    lhs=log2(c0)+totient(F)-log2(F)
    rhs=1+(1+log(F,3))*log2(C)
    if lhs<rhs: bad.append(F)
print(bad, max(bad))
# tail with phi>=sqrt(F/2)
for F in [1000,2000,5000,10**4]:
    print(F, log2(c0)+sqrt(F/2)-log2(F) - (1+(1+log(F,3))*log2(C)))
