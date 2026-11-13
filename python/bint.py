from math import prod, log, log2, sqrt
from sympy import totient, divisors
import json,sys
C=1.0
for v in range(2,300): C/= (1-2.0**-v)
c0=1.0
for d in range(1,300): c0*=(1-2.0**-d)
def exc(t,Fmax=20000):
    E=[]
    for F in range(2,Fmax):
        if c0*2.0**min(totient(F),1000)/F <= 2.0**t * C**(1+log(F,3)):
            E.append(F)
    return E
def parts(n, divs, maxpart, cap=None, used=None):
    if n==0: yield []; return
    for d in divs:
        if d<=maxpart and d<=n:
            for r in parts(n-d, divs, d):
                yield [d]+r
def N2(d):
    from sympy import mobius
    return sum(mobius(d//e)*2**e for e in divisors(d))//d
out={}
for t in range(int(sys.argv[1]),int(sys.argv[2])):
    E=exc(t)
    sols=[]; cnt=0
    for F in E:
        if F-t<0: continue
        divs=sorted([d for d in divisors(F) if 2<=d<F],reverse=True)
        for S in parts(F-t,divs,F):
            if len(S)+t<2: continue
            cnt+=1
            if (2**F-1)%prod(2**f-1 for f in S)==0: sols.append((F,tuple(S)))
    print('t',t,'maxF',max(E),'|E|',len(E),'cands',cnt,'sols',sols,flush=True)
    out[t]={'E':E,'sols':sols,'cands':cnt}
json.dump(out,open('bint_'+sys.argv[1]+'.json','w'))
