import itertools
from math import prod
cnt=0
for size in range(2,10):
    for S in itertools.combinations_with_replacement(range(2,17),size):
        F=sum(S)
        if all(F%f==0 for f in S):
            if (2**F-1)%prod(2**f-1 for f in S)==0: print('t0',S)
        # t=1
        F1=F+1
        if all(F1%f==0 for f in S) and (2**F1-1)%prod(2**f-1 for f in S)==0: print('t1',S)
