# emulate Lean binSols exactly and emit per-(t,F) theorems
import json,sys
sys.setrecursionlimit(10000)
from functools import lru_cache
d={}
for f in ['bint.json','bint_5.json','bint_9.json']: d.update(json.load(open('../python/'+f)))
E={}
for line in open('./elist.txt'):
    t,s=line.split(); E[int(t)]=[int(x) for x in s.split(',')]
def parts(ds,mx,n):
    if n==0: return [[]]
    out=[]
    for dd in ds:
        if dd<=mx and dd<=n and dd>0:
            out+= [[dd]+r for r in parts(ds,dd,n-dd)]
    return out
def prod(l):
    r=1
    for x in l: r*=x
    return r
def binSols(t,F):
    if F<t: return []
    ds=[x for x in range(F) if x>=2 and F%x==0][::-1]
    return [S for S in parts(ds,F,F-t) if S and 2<=t+len(S) and (2**F-1)%prod([2**f-1 for f in S])==0]
lines=[]; total=0
for t in range(13):
    ref=sorted(tuple(sorted(S)) for F,S in d[str(t)]['sols'] if S)
    got=[]
    for F in E[t]:
        sols=binSols(t,F); got+= [tuple(sorted(S)) for S in sols]
        lines.append(f"theorem bin_t{t}_F{F} : binSols {t} {F} = {json.dumps(sols).replace(' ','').replace(',',', ')} := by decide +kernel")
        total+=1
    assert sorted(got)==ref,(t,sorted(got),ref)
open('./binsplit.txt','w').write("\n".join(lines)+"\n")
print(total)
