import itertools,sys
from math import prod
def ok(S,t,q=2,sign=-1):
    F=sum(S)+t
    return (q**F+ (1 if sign>0 else -1)) % prod(q**f-1 for f in S)==0
# t=0, multisets of f>=2 up to size 6, f<=12
for size in range(1,7):
    for S in itertools.combinations_with_replacement(range(2,13),size):
        for t in range(0,13):
            if size+t<2: continue
            if ok(S,t): 
                if t<=3 or size>=2: print('L',S,t)
