import json,re,sys
from math import prod
d={}
for f in ['bint.json','bint_5.json','bint_9.json']: d.update(json.load(open('../python/'+f)))
E={}
for line in open('./elist.txt'):
    t,s=line.split(); E[int(t)]=[int(x) for x in s.split(',')]
def base(q):
    for p in range(2,q+1):
        if q%p==0:
            f=0; r=q
            while r%p==0: r//=p; f+=1
            assert r==1; return p,f
oddL=[]; oddC=[]
for f,lst in [('uni.log',None)]:
    pass
for line in open('../logs/uni.log'):
    pass
# parse with signs
L=[];C=[]
mode=None
for line in open('../logs/julia_search_all.log'):
    if line.startswith('mode='):
        mode=line.split()[0][5:]; eps=int(line.split()[1][4:])
    elif line.strip().startswith('SOL') and mode=='U':
        Q=[int(x) for x in line.split(':')[1].split()]
        (L if eps<0 else C).append(Q)
L.append([3,3,3,3,5,5,89])
out=[]
out.append("""/-
  Lean 4 certificate for "Lehmer's Totient Problem for Ideals of Dedekind Domains".
  Core library only.  Every statement is closed by `decide +kernel`, i.e. evaluated by the
  kernel; no `sorry`, no axiom beyond the kernel's own, no `native_decide`.
-/

/-- nonincreasing lists of elements of `ds` (listed in decreasing order) with sum `n` and
largest part at most `mx`; `fuel` bounds the depth of recursion. -/
def parts : Nat → List Nat → Nat → Nat → List (List Nat)
  | 0, _, _, _ => []
  | fuel+1, ds, mx, n =>
    if n = 0 then [[]] else
    ds.flatMap (fun d => if d ≤ mx ∧ d ≤ n ∧ 0 < d then (parts fuel ds d (n - d)).map (d :: ·) else [])

def listProd (l : List Nat) : Nat := l.foldl (· * ·) 1

/-! ## Section 4: multisets of powers of two -/

/-- nonincreasing lists `S` of elements of `ds` (given in decreasing order), with sum `n`, largest
part at most `mx`, such that `acc * ∏_{f∈S} (2^f-1)` divides `N`.  Since a product divides `N`
only if each partial product does, pruning on divisibility loses no solution. -/
def bparts (N : Nat) : Nat → List Nat → Nat → Nat → Nat → List (List Nat)
  | 0, _, _, _, _ => []
  | fuel+1, ds, mx, n, acc =>
    if n = 0 then [[]] else
    ds.flatMap (fun d =>
      if d ≤ mx ∧ d ≤ n ∧ 0 < d ∧ N % (acc * (2^d - 1)) = 0 then
        (bparts N fuel ds d (n - d) (acc * (2^d - 1))).map (d :: ·)
      else [])

/-- divisors `d` of `F` with `lo ≤ d < F`, in decreasing order -/
def divsFrom (lo F : Nat) : List Nat :=
  ((List.range F).filter (fun d => lo ≤ d ∧ F % d = 0)).reverse

/-- all exponent multisets `S ≠ ∅` of proper divisors `f ≥ 2` of `F` with `t + Σ S = F`,
`t + |S| ≥ 2`, and `∏_{f∈S} (2^f-1) ∣ 2^F-1` -/
def binSols (t F : Nat) : List (List Nat) :=
  if F < t then [] else
  (bparts (2^F - 1) (F+1) (divsFrom 2 F) F (F - t) 1).filter (fun S => S ≠ [] ∧ 2 ≤ t + S.length)
""")
bs=open('./binsplit.txt').read().splitlines()
for t in range(13):
    out.append(f"/-- Theorem 4.4, t = {t}: for every F in the candidate set E_{t} of Theorem 4.3, the complete list of exponent multisets S. -/")
    out+= [l for l in bs if l.startswith(f"theorem bin_t{t}_F")]
    out.append("")
out.append("""/-- Proposition 4.5(b) and Theorem 4.7 on a finite range: for `1 ≤ t ≤ 40`, `1 ≤ c ≤ 7`,
`3^c ∣ 2^(t+2c) - 1` iff `t` even and `3^(c-1) ∣ t+2c`, and `3^c ∣ 2^(t+2c) + 1` iff `t` odd and
`3^(c-1) ∣ t+2c`. -/
theorem bin_three_adic :
    ((List.range 40).all fun t => (List.range 7).all fun c =>
      let t := t + 1; let c := c + 1; let F := t + 2*c
      ((2^F - 1) % 3^c == 0) == (t % 2 == 0 && F % 3^(c-1) == 0) &&
      ((2^F + 1) % 3^c == 0) == (t % 2 == 1 && F % 3^(c-1) == 0)) = true := by decide +kernel

/-- companion: an exponent `f ≥ 3` never gives `2^f - 1 ∣ 2^F + 1` (checked for `f ≤ 30`, `F ≤ 120`) -/
theorem bin_comp_exponent :
    ((List.range 28).all fun f => (List.range 120).all fun F =>
      (2^F + 1) % (2^(f+3) - 1) != 0) = true := by decide +kernel

/-! ## Section 5: powers of one odd prime -/

def oneLehmer (p F : Nat) (S : List Nat) : Bool := (p^F - 1) % listProd (S.map (fun f => p^f - 1)) == 0

def oneSols (p F kmax : Nat) : List (List Nat) :=
  ((parts (F+1) (divsFrom 1 F) F F).filter (fun S => 2 ≤ S.length ∧ S.length ≤ kmax)).filter (oneLehmer p F)

/-- Theorem 5.1(a), the finite part for `p = 3`: `F ∈ {2,3,4,6,8,10,12}`, `|S| ≤ log₂(4F)`. -/
theorem one_p3 :
    ([2,3,4,6,8,10,12].flatMap fun F => (oneSols 3 F (Nat.log2 (4*F))).map (fun S => (F, S)))
      = [(2, [1, 1]), (4, [1, 1, 1, 1])] := by decide +kernel

/-- Theorem 5.1(a), the finite part for `p = 5`: `F ∈ {2,6}`, `|S| ≤ log₂(12F)`. -/
theorem one_p5 :
    ([2,6].flatMap fun F => (oneSols 5 F (Nat.log2 (12*F))).map (fun S => (F, S))) = [] := by decide +kernel

/-- the two solutions -/
theorem one_sols : (3^2 - 1) % ((3-1)*(3-1)) = 0 ∧ (3^4 - 1) % ((3-1)^4) = 0 ∧
    (3^2-1)/((3-1)^2) = 2 ∧ (3^4-1)/((3-1)^4) = 5 := by decide +kernel

/-! ## Sections 6-8: odd multisets with several primes -/

/-- a multiset given as a list of pairs `(p, f)` (member `p^f`) is `ε`-admissible with quotient `M`
and satisfies the independence condition -/
def admissible (eps : Int) (M : Nat) (Q : List (Nat × Nat)) : Bool :=
  let N : Nat := listProd (Q.map fun (p, f) => p^f)
  let φ : Nat := listProd (Q.map fun (p, f) => p^f - 1)
  let indep := Q.all fun (p, _) => (Q.all fun (p', f') => p == p' || (p'^f' - 1) % p != 0) && M % p != 0
  2 ≤ Q.length && 1 < φ && indep && ((N : Int) + eps == (M : Int) * (φ : Int))
""")
def pairs(Q): return "["+", ".join("(%d, %d)"%base(q) for q in Q)+"]"
def M_of(Q,eps):
    N=prod(Q); ph=prod(q-1 for q in Q); assert (N+eps)%ph==0; return (N+eps)//ph
out.append("/-- Theorem 7.1(a): the five odd Lehmer multisets with at most seven members -/")
out.append("theorem odd_lehmer :")
out.append("    ("+ " &&\n     ".join(f"admissible (-1) {M_of(Q,-1)} {pairs(Q)}" for Q in L) +") = true := by decide +kernel\n")
out.append("/-- Theorem 7.1(b): the odd companion multisets with at most six members -/")
out.append("theorem odd_companion :")
out.append("    ("+ " &&\n     ".join(f"admissible 1 {M_of(Q,1)} {pairs(Q)}" for Q in C) +") = true := by decide +kernel\n")
out.append("""/-- Proposition 7.3: the numbers behind the biquadratic Lehmer ideal in `ℚ(i, √89)`:
`5 ≡ 1 (mod 4)`, `89 ≡ 2² (mod 5)`, `89 ≡ 2 (mod 3)` (a non-square), `-89 ≡ 1 (mod 3)`,
`89 ≡ 1 (mod 4)`, and `N = 180225 = 2·90112 + 1`. -/
theorem biquad : 5 % 4 = 1 ∧ 89 % 5 = 2^2 % 5 ∧ 89 % 3 = 2 ∧ (3 - 89 % 3) % 3 = 1 ∧ 89 % 4 = 1 ∧
    5*5*9*9*89 = 180225 ∧ 4*4*8*8*88 = 90112 ∧ 180225 = 2*90112 + 1 ∧ 180224 = 2^14 * 11 := by
  decide +kernel

/-- Example 6.6: `x⁴+x+2 ≡ x(x+1)(x²+x+1) (mod 2)`, coefficients listed from degree 0;
the product `x(x+1)(x²+x+1) = x⁴ + x` over `𝔽₂`. -/
theorem quartic_mod2 : [2 % 2, 1, 0, 0, 1] = [0, 1, 0, 0, 1] ∧ (2*2*4 - 1) % 3 = 0 ∧ (2*4 + 1) % 3 = 0 := by
  decide +kernel

/-- Corollary 6.2: `x(x²+x+1)` over `𝔽₂` has `φ = 3` and norm `2³ = 8`, so `3 ∣ 8 + 1`;
`x(x+1)(x²+x+1)` has `φ = 3` and norm `16`, so `3 ∣ 16 - 1`; `{2,4,8}` gives `21 ∣ 63`. -/
theorem fqx : (8 + 1) % 3 = 0 ∧ (16 - 1) % 3 = 0 ∧ (64 - 1) % (3 * 7) = 0 := by decide +kernel
""")

out.append("""
/-- Proposition 7.5: the companion multiset of mode Q with seven members -/
theorem quad_companion :
    admissible 1 2 [(5, 1), (7, 1), (7, 1), (13, 1), (13, 1), (619, 1), (25629697, 1)] = true := by
  decide +kernel
""")
for n in [l.split()[1] for l in bs]+["bin_three_adic","bin_comp_exponent","one_p3","one_p5","one_sols","odd_lehmer","odd_companion","quad_companion","biquad","quartic_mod2","fqx"]:
    out.append("#print axioms "+n)
out.append("")
open('LehmerIdeals.lean','w').write("\n".join(out))
print(len(L),len(C))
