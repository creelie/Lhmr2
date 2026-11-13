# Lehmer multisets search: odd prime powers, multiplicity rule
import sys
from sympy import isprime, perfect_power, primerange
from math import isqrt
def is_ppow(n):
    if n<3 or n%2==0: return False
    if isprime(n): return True
    pp=perfect_power(n)
    return bool(pp) and isprime(pp[0])
def iroot_floor_frac(num,den,m):
    pass
def search(k, mode, sign=-1, Mmax=None, qmax_step=10**7):
    # mode: 'int' distinct primes ; 'uni' any odd prime power any multiplicity
    sols=[]; nodes=[0]
    Ms = range(2, (Mmax or int(1.5**k)+1)+1)
    def ok_next(prev,q,mult):
        if mode=='int': return q>prev and isprime(q)
        if mode=='uni': return q>=prev and is_ppow(q)
    def rec(A,B,j,prev,seq,M):
        nodes[0]+=1
        m=k-j
        # lower: A q < M B (q-1) -> q > MB/(MB-A)   (need MB>A)
        if M*B<=A: return
        lo=max(prev, M*B//(M*B-A)+1)
        if m==1:
            return
        # upper: A q^m > M B (q-1)^m  ; find largest q by binary search
        def reach(q): return A*q**m > M*B*(q-1)**m
        if not reach(lo): return
        hi=lo
        while reach(hi*2): hi*=2
        a,b=hi,hi*2
        while b-a>1:
            c=(a+b)//2
            if reach(c): a=c
            else: b=c
        hi=a
        if m==2:
            # q_{k-1}=q, q_k = (M B' - sign... ) general: A' q_k - (sign stuff)
            q=lo
            while q<=hi:
                if ok_next(prev,q,None):
                    A2=A*q;B2=B*(q-1)
                    # A2 x + sign = M B2 (x-1)  -> x (M B2 - A2) = M B2 + sign
                    den=M*B2-A2
                    if den>0 and (M*B2+sign)%den==0:
                        x=(M*B2+sign)//den
                        if ok_next(q,x,None):
                            sols.append(tuple(seq+[q,x]))
                q+=1 if mode=='uni' else (1 if q<3 else 2)
                if q%2==0: q+=1
            return
        q=lo|1
        while q<=hi:
            if ok_next(prev,q,None):
                rec(A*q,B*(q-1),j+1,q,seq+[q],M)
            q+=2
    for M in Ms:
        rec(1,1,0,2 if mode=='uni' else 2,[],M)
    return sols,nodes[0]
if __name__=='__main__':
    mode=sys.argv[1]; sign=int(sys.argv[2])
    for k in range(2,int(sys.argv[3])+1):
        s,n=search(k,mode,sign)
        print(k,n,s,flush=True)
