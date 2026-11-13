/-
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

/-- Theorem 4.4, t = 0: for every F in the candidate set E_0 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t0_F3 : binSols 0 3 = [] := by decide +kernel
theorem bin_t0_F4 : binSols 0 4 = [] := by decide +kernel
theorem bin_t0_F5 : binSols 0 5 = [] := by decide +kernel
theorem bin_t0_F6 : binSols 0 6 = [] := by decide +kernel
theorem bin_t0_F7 : binSols 0 7 = [] := by decide +kernel
theorem bin_t0_F8 : binSols 0 8 = [] := by decide +kernel
theorem bin_t0_F9 : binSols 0 9 = [] := by decide +kernel
theorem bin_t0_F10 : binSols 0 10 = [] := by decide +kernel
theorem bin_t0_F12 : binSols 0 12 = [] := by decide +kernel
theorem bin_t0_F14 : binSols 0 14 = [] := by decide +kernel
theorem bin_t0_F15 : binSols 0 15 = [] := by decide +kernel
theorem bin_t0_F16 : binSols 0 16 = [] := by decide +kernel
theorem bin_t0_F18 : binSols 0 18 = [] := by decide +kernel
theorem bin_t0_F20 : binSols 0 20 = [] := by decide +kernel
theorem bin_t0_F24 : binSols 0 24 = [] := by decide +kernel
theorem bin_t0_F30 : binSols 0 30 = [] := by decide +kernel

/-- Theorem 4.4, t = 1: for every F in the candidate set E_1 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t1_F3 : binSols 1 3 = [] := by decide +kernel
theorem bin_t1_F4 : binSols 1 4 = [] := by decide +kernel
theorem bin_t1_F5 : binSols 1 5 = [] := by decide +kernel
theorem bin_t1_F6 : binSols 1 6 = [[3, 2]] := by decide +kernel
theorem bin_t1_F7 : binSols 1 7 = [] := by decide +kernel
theorem bin_t1_F8 : binSols 1 8 = [] := by decide +kernel
theorem bin_t1_F9 : binSols 1 9 = [] := by decide +kernel
theorem bin_t1_F10 : binSols 1 10 = [] := by decide +kernel
theorem bin_t1_F12 : binSols 1 12 = [] := by decide +kernel
theorem bin_t1_F14 : binSols 1 14 = [] := by decide +kernel
theorem bin_t1_F15 : binSols 1 15 = [] := by decide +kernel
theorem bin_t1_F16 : binSols 1 16 = [] := by decide +kernel
theorem bin_t1_F18 : binSols 1 18 = [] := by decide +kernel
theorem bin_t1_F20 : binSols 1 20 = [] := by decide +kernel
theorem bin_t1_F22 : binSols 1 22 = [] := by decide +kernel
theorem bin_t1_F24 : binSols 1 24 = [] := by decide +kernel
theorem bin_t1_F30 : binSols 1 30 = [] := by decide +kernel

/-- Theorem 4.4, t = 2: for every F in the candidate set E_2 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t2_F3 : binSols 2 3 = [] := by decide +kernel
theorem bin_t2_F4 : binSols 2 4 = [[2]] := by decide +kernel
theorem bin_t2_F5 : binSols 2 5 = [] := by decide +kernel
theorem bin_t2_F6 : binSols 2 6 = [[2, 2]] := by decide +kernel
theorem bin_t2_F7 : binSols 2 7 = [] := by decide +kernel
theorem bin_t2_F8 : binSols 2 8 = [] := by decide +kernel
theorem bin_t2_F9 : binSols 2 9 = [] := by decide +kernel
theorem bin_t2_F10 : binSols 2 10 = [] := by decide +kernel
theorem bin_t2_F12 : binSols 2 12 = [] := by decide +kernel
theorem bin_t2_F14 : binSols 2 14 = [] := by decide +kernel
theorem bin_t2_F15 : binSols 2 15 = [] := by decide +kernel
theorem bin_t2_F16 : binSols 2 16 = [] := by decide +kernel
theorem bin_t2_F18 : binSols 2 18 = [] := by decide +kernel
theorem bin_t2_F20 : binSols 2 20 = [] := by decide +kernel
theorem bin_t2_F22 : binSols 2 22 = [] := by decide +kernel
theorem bin_t2_F24 : binSols 2 24 = [] := by decide +kernel
theorem bin_t2_F30 : binSols 2 30 = [] := by decide +kernel
theorem bin_t2_F36 : binSols 2 36 = [] := by decide +kernel
theorem bin_t2_F42 : binSols 2 42 = [] := by decide +kernel

/-- Theorem 4.4, t = 3: for every F in the candidate set E_3 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t3_F3 : binSols 3 3 = [] := by decide +kernel
theorem bin_t3_F4 : binSols 3 4 = [] := by decide +kernel
theorem bin_t3_F5 : binSols 3 5 = [] := by decide +kernel
theorem bin_t3_F6 : binSols 3 6 = [[3]] := by decide +kernel
theorem bin_t3_F7 : binSols 3 7 = [] := by decide +kernel
theorem bin_t3_F8 : binSols 3 8 = [] := by decide +kernel
theorem bin_t3_F9 : binSols 3 9 = [] := by decide +kernel
theorem bin_t3_F10 : binSols 3 10 = [[5, 2]] := by decide +kernel
theorem bin_t3_F11 : binSols 3 11 = [] := by decide +kernel
theorem bin_t3_F12 : binSols 3 12 = [[4, 3, 2]] := by decide +kernel
theorem bin_t3_F14 : binSols 3 14 = [] := by decide +kernel
theorem bin_t3_F15 : binSols 3 15 = [] := by decide +kernel
theorem bin_t3_F16 : binSols 3 16 = [] := by decide +kernel
theorem bin_t3_F18 : binSols 3 18 = [[9, 2, 2, 2]] := by decide +kernel
theorem bin_t3_F20 : binSols 3 20 = [] := by decide +kernel
theorem bin_t3_F21 : binSols 3 21 = [] := by decide +kernel
theorem bin_t3_F22 : binSols 3 22 = [] := by decide +kernel
theorem bin_t3_F24 : binSols 3 24 = [] := by decide +kernel
theorem bin_t3_F26 : binSols 3 26 = [] := by decide +kernel
theorem bin_t3_F28 : binSols 3 28 = [] := by decide +kernel
theorem bin_t3_F30 : binSols 3 30 = [] := by decide +kernel
theorem bin_t3_F36 : binSols 3 36 = [] := by decide +kernel
theorem bin_t3_F42 : binSols 3 42 = [] := by decide +kernel

/-- Theorem 4.4, t = 4: for every F in the candidate set E_4 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t4_F3 : binSols 4 3 = [] := by decide +kernel
theorem bin_t4_F4 : binSols 4 4 = [] := by decide +kernel
theorem bin_t4_F5 : binSols 4 5 = [] := by decide +kernel
theorem bin_t4_F6 : binSols 4 6 = [[2]] := by decide +kernel
theorem bin_t4_F7 : binSols 4 7 = [] := by decide +kernel
theorem bin_t4_F8 : binSols 4 8 = [[4]] := by decide +kernel
theorem bin_t4_F9 : binSols 4 9 = [] := by decide +kernel
theorem bin_t4_F10 : binSols 4 10 = [] := by decide +kernel
theorem bin_t4_F11 : binSols 4 11 = [] := by decide +kernel
theorem bin_t4_F12 : binSols 4 12 = [] := by decide +kernel
theorem bin_t4_F13 : binSols 4 13 = [] := by decide +kernel
theorem bin_t4_F14 : binSols 4 14 = [] := by decide +kernel
theorem bin_t4_F15 : binSols 4 15 = [] := by decide +kernel
theorem bin_t4_F16 : binSols 4 16 = [] := by decide +kernel
theorem bin_t4_F18 : binSols 4 18 = [] := by decide +kernel
theorem bin_t4_F20 : binSols 4 20 = [] := by decide +kernel
theorem bin_t4_F21 : binSols 4 21 = [] := by decide +kernel
theorem bin_t4_F22 : binSols 4 22 = [] := by decide +kernel
theorem bin_t4_F24 : binSols 4 24 = [] := by decide +kernel
theorem bin_t4_F26 : binSols 4 26 = [] := by decide +kernel
theorem bin_t4_F28 : binSols 4 28 = [] := by decide +kernel
theorem bin_t4_F30 : binSols 4 30 = [] := by decide +kernel
theorem bin_t4_F36 : binSols 4 36 = [] := by decide +kernel
theorem bin_t4_F42 : binSols 4 42 = [] := by decide +kernel

/-- Theorem 4.4, t = 5: for every F in the candidate set E_5 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t5_F3 : binSols 5 3 = [] := by decide +kernel
theorem bin_t5_F4 : binSols 5 4 = [] := by decide +kernel
theorem bin_t5_F5 : binSols 5 5 = [] := by decide +kernel
theorem bin_t5_F6 : binSols 5 6 = [] := by decide +kernel
theorem bin_t5_F7 : binSols 5 7 = [] := by decide +kernel
theorem bin_t5_F8 : binSols 5 8 = [] := by decide +kernel
theorem bin_t5_F9 : binSols 5 9 = [] := by decide +kernel
theorem bin_t5_F10 : binSols 5 10 = [[5]] := by decide +kernel
theorem bin_t5_F11 : binSols 5 11 = [] := by decide +kernel
theorem bin_t5_F12 : binSols 5 12 = [[4, 3], [3, 2, 2]] := by decide +kernel
theorem bin_t5_F13 : binSols 5 13 = [] := by decide +kernel
theorem bin_t5_F14 : binSols 5 14 = [[7, 2]] := by decide +kernel
theorem bin_t5_F15 : binSols 5 15 = [] := by decide +kernel
theorem bin_t5_F16 : binSols 5 16 = [] := by decide +kernel
theorem bin_t5_F18 : binSols 5 18 = [[9, 2, 2]] := by decide +kernel
theorem bin_t5_F20 : binSols 5 20 = [] := by decide +kernel
theorem bin_t5_F21 : binSols 5 21 = [] := by decide +kernel
theorem bin_t5_F22 : binSols 5 22 = [] := by decide +kernel
theorem bin_t5_F24 : binSols 5 24 = [] := by decide +kernel
theorem bin_t5_F26 : binSols 5 26 = [] := by decide +kernel
theorem bin_t5_F28 : binSols 5 28 = [] := by decide +kernel
theorem bin_t5_F30 : binSols 5 30 = [] := by decide +kernel
theorem bin_t5_F36 : binSols 5 36 = [] := by decide +kernel
theorem bin_t5_F42 : binSols 5 42 = [] := by decide +kernel
theorem bin_t5_F60 : binSols 5 60 = [] := by decide +kernel

/-- Theorem 4.4, t = 6: for every F in the candidate set E_6 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t6_F3 : binSols 6 3 = [] := by decide +kernel
theorem bin_t6_F4 : binSols 6 4 = [] := by decide +kernel
theorem bin_t6_F5 : binSols 6 5 = [] := by decide +kernel
theorem bin_t6_F6 : binSols 6 6 = [] := by decide +kernel
theorem bin_t6_F7 : binSols 6 7 = [] := by decide +kernel
theorem bin_t6_F8 : binSols 6 8 = [[2]] := by decide +kernel
theorem bin_t6_F9 : binSols 6 9 = [[3]] := by decide +kernel
theorem bin_t6_F10 : binSols 6 10 = [] := by decide +kernel
theorem bin_t6_F11 : binSols 6 11 = [] := by decide +kernel
theorem bin_t6_F12 : binSols 6 12 = [[6], [4, 2]] := by decide +kernel
theorem bin_t6_F13 : binSols 6 13 = [] := by decide +kernel
theorem bin_t6_F14 : binSols 6 14 = [] := by decide +kernel
theorem bin_t6_F15 : binSols 6 15 = [] := by decide +kernel
theorem bin_t6_F16 : binSols 6 16 = [] := by decide +kernel
theorem bin_t6_F18 : binSols 6 18 = [] := by decide +kernel
theorem bin_t6_F20 : binSols 6 20 = [] := by decide +kernel
theorem bin_t6_F21 : binSols 6 21 = [] := by decide +kernel
theorem bin_t6_F22 : binSols 6 22 = [] := by decide +kernel
theorem bin_t6_F24 : binSols 6 24 = [] := by decide +kernel
theorem bin_t6_F26 : binSols 6 26 = [] := by decide +kernel
theorem bin_t6_F28 : binSols 6 28 = [] := by decide +kernel
theorem bin_t6_F30 : binSols 6 30 = [] := by decide +kernel
theorem bin_t6_F32 : binSols 6 32 = [] := by decide +kernel
theorem bin_t6_F34 : binSols 6 34 = [] := by decide +kernel
theorem bin_t6_F36 : binSols 6 36 = [] := by decide +kernel
theorem bin_t6_F40 : binSols 6 40 = [] := by decide +kernel
theorem bin_t6_F42 : binSols 6 42 = [] := by decide +kernel
theorem bin_t6_F48 : binSols 6 48 = [] := by decide +kernel
theorem bin_t6_F60 : binSols 6 60 = [] := by decide +kernel

/-- Theorem 4.4, t = 7: for every F in the candidate set E_7 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t7_F3 : binSols 7 3 = [] := by decide +kernel
theorem bin_t7_F4 : binSols 7 4 = [] := by decide +kernel
theorem bin_t7_F5 : binSols 7 5 = [] := by decide +kernel
theorem bin_t7_F6 : binSols 7 6 = [] := by decide +kernel
theorem bin_t7_F7 : binSols 7 7 = [] := by decide +kernel
theorem bin_t7_F8 : binSols 7 8 = [] := by decide +kernel
theorem bin_t7_F9 : binSols 7 9 = [] := by decide +kernel
theorem bin_t7_F10 : binSols 7 10 = [] := by decide +kernel
theorem bin_t7_F11 : binSols 7 11 = [] := by decide +kernel
theorem bin_t7_F12 : binSols 7 12 = [[3, 2]] := by decide +kernel
theorem bin_t7_F13 : binSols 7 13 = [] := by decide +kernel
theorem bin_t7_F14 : binSols 7 14 = [[7]] := by decide +kernel
theorem bin_t7_F15 : binSols 7 15 = [[5, 3]] := by decide +kernel
theorem bin_t7_F16 : binSols 7 16 = [] := by decide +kernel
theorem bin_t7_F18 : binSols 7 18 = [[9, 2]] := by decide +kernel
theorem bin_t7_F20 : binSols 7 20 = [] := by decide +kernel
theorem bin_t7_F21 : binSols 7 21 = [] := by decide +kernel
theorem bin_t7_F22 : binSols 7 22 = [] := by decide +kernel
theorem bin_t7_F24 : binSols 7 24 = [] := by decide +kernel
theorem bin_t7_F26 : binSols 7 26 = [] := by decide +kernel
theorem bin_t7_F28 : binSols 7 28 = [] := by decide +kernel
theorem bin_t7_F30 : binSols 7 30 = [] := by decide +kernel
theorem bin_t7_F32 : binSols 7 32 = [] := by decide +kernel
theorem bin_t7_F34 : binSols 7 34 = [] := by decide +kernel
theorem bin_t7_F36 : binSols 7 36 = [] := by decide +kernel
theorem bin_t7_F40 : binSols 7 40 = [] := by decide +kernel
theorem bin_t7_F42 : binSols 7 42 = [] := by decide +kernel
theorem bin_t7_F48 : binSols 7 48 = [] := by decide +kernel
theorem bin_t7_F54 : binSols 7 54 = [] := by decide +kernel
theorem bin_t7_F60 : binSols 7 60 = [] := by decide +kernel

/-- Theorem 4.4, t = 8: for every F in the candidate set E_8 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t8_F3 : binSols 8 3 = [] := by decide +kernel
theorem bin_t8_F4 : binSols 8 4 = [] := by decide +kernel
theorem bin_t8_F5 : binSols 8 5 = [] := by decide +kernel
theorem bin_t8_F6 : binSols 8 6 = [] := by decide +kernel
theorem bin_t8_F7 : binSols 8 7 = [] := by decide +kernel
theorem bin_t8_F8 : binSols 8 8 = [] := by decide +kernel
theorem bin_t8_F9 : binSols 8 9 = [] := by decide +kernel
theorem bin_t8_F10 : binSols 8 10 = [[2]] := by decide +kernel
theorem bin_t8_F11 : binSols 8 11 = [] := by decide +kernel
theorem bin_t8_F12 : binSols 8 12 = [[4], [2, 2]] := by decide +kernel
theorem bin_t8_F13 : binSols 8 13 = [] := by decide +kernel
theorem bin_t8_F14 : binSols 8 14 = [] := by decide +kernel
theorem bin_t8_F15 : binSols 8 15 = [] := by decide +kernel
theorem bin_t8_F16 : binSols 8 16 = [[8]] := by decide +kernel
theorem bin_t8_F17 : binSols 8 17 = [] := by decide +kernel
theorem bin_t8_F18 : binSols 8 18 = [] := by decide +kernel
theorem bin_t8_F20 : binSols 8 20 = [] := by decide +kernel
theorem bin_t8_F21 : binSols 8 21 = [[7, 3, 3]] := by decide +kernel
theorem bin_t8_F22 : binSols 8 22 = [] := by decide +kernel
theorem bin_t8_F24 : binSols 8 24 = [] := by decide +kernel
theorem bin_t8_F26 : binSols 8 26 = [] := by decide +kernel
theorem bin_t8_F28 : binSols 8 28 = [] := by decide +kernel
theorem bin_t8_F30 : binSols 8 30 = [] := by decide +kernel
theorem bin_t8_F32 : binSols 8 32 = [] := by decide +kernel
theorem bin_t8_F34 : binSols 8 34 = [] := by decide +kernel
theorem bin_t8_F36 : binSols 8 36 = [] := by decide +kernel
theorem bin_t8_F38 : binSols 8 38 = [] := by decide +kernel
theorem bin_t8_F40 : binSols 8 40 = [] := by decide +kernel
theorem bin_t8_F42 : binSols 8 42 = [] := by decide +kernel
theorem bin_t8_F48 : binSols 8 48 = [] := by decide +kernel
theorem bin_t8_F54 : binSols 8 54 = [] := by decide +kernel
theorem bin_t8_F60 : binSols 8 60 = [] := by decide +kernel

/-- Theorem 4.4, t = 9: for every F in the candidate set E_9 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t9_F3 : binSols 9 3 = [] := by decide +kernel
theorem bin_t9_F4 : binSols 9 4 = [] := by decide +kernel
theorem bin_t9_F5 : binSols 9 5 = [] := by decide +kernel
theorem bin_t9_F6 : binSols 9 6 = [] := by decide +kernel
theorem bin_t9_F7 : binSols 9 7 = [] := by decide +kernel
theorem bin_t9_F8 : binSols 9 8 = [] := by decide +kernel
theorem bin_t9_F9 : binSols 9 9 = [] := by decide +kernel
theorem bin_t9_F10 : binSols 9 10 = [] := by decide +kernel
theorem bin_t9_F11 : binSols 9 11 = [] := by decide +kernel
theorem bin_t9_F12 : binSols 9 12 = [[3]] := by decide +kernel
theorem bin_t9_F13 : binSols 9 13 = [] := by decide +kernel
theorem bin_t9_F14 : binSols 9 14 = [] := by decide +kernel
theorem bin_t9_F15 : binSols 9 15 = [] := by decide +kernel
theorem bin_t9_F16 : binSols 9 16 = [] := by decide +kernel
theorem bin_t9_F17 : binSols 9 17 = [] := by decide +kernel
theorem bin_t9_F18 : binSols 9 18 = [[9], [3, 2, 2, 2]] := by decide +kernel
theorem bin_t9_F20 : binSols 9 20 = [] := by decide +kernel
theorem bin_t9_F21 : binSols 9 21 = [] := by decide +kernel
theorem bin_t9_F22 : binSols 9 22 = [[11, 2]] := by decide +kernel
theorem bin_t9_F24 : binSols 9 24 = [] := by decide +kernel
theorem bin_t9_F26 : binSols 9 26 = [] := by decide +kernel
theorem bin_t9_F27 : binSols 9 27 = [] := by decide +kernel
theorem bin_t9_F28 : binSols 9 28 = [] := by decide +kernel
theorem bin_t9_F30 : binSols 9 30 = [] := by decide +kernel
theorem bin_t9_F32 : binSols 9 32 = [] := by decide +kernel
theorem bin_t9_F34 : binSols 9 34 = [] := by decide +kernel
theorem bin_t9_F36 : binSols 9 36 = [] := by decide +kernel
theorem bin_t9_F38 : binSols 9 38 = [] := by decide +kernel
theorem bin_t9_F40 : binSols 9 40 = [] := by decide +kernel
theorem bin_t9_F42 : binSols 9 42 = [] := by decide +kernel
theorem bin_t9_F48 : binSols 9 48 = [] := by decide +kernel
theorem bin_t9_F50 : binSols 9 50 = [] := by decide +kernel
theorem bin_t9_F54 : binSols 9 54 = [] := by decide +kernel
theorem bin_t9_F60 : binSols 9 60 = [] := by decide +kernel
theorem bin_t9_F66 : binSols 9 66 = [] := by decide +kernel

/-- Theorem 4.4, t = 10: for every F in the candidate set E_10 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t10_F3 : binSols 10 3 = [] := by decide +kernel
theorem bin_t10_F4 : binSols 10 4 = [] := by decide +kernel
theorem bin_t10_F5 : binSols 10 5 = [] := by decide +kernel
theorem bin_t10_F6 : binSols 10 6 = [] := by decide +kernel
theorem bin_t10_F7 : binSols 10 7 = [] := by decide +kernel
theorem bin_t10_F8 : binSols 10 8 = [] := by decide +kernel
theorem bin_t10_F9 : binSols 10 9 = [] := by decide +kernel
theorem bin_t10_F10 : binSols 10 10 = [] := by decide +kernel
theorem bin_t10_F11 : binSols 10 11 = [] := by decide +kernel
theorem bin_t10_F12 : binSols 10 12 = [[2]] := by decide +kernel
theorem bin_t10_F13 : binSols 10 13 = [] := by decide +kernel
theorem bin_t10_F14 : binSols 10 14 = [] := by decide +kernel
theorem bin_t10_F15 : binSols 10 15 = [[5]] := by decide +kernel
theorem bin_t10_F16 : binSols 10 16 = [] := by decide +kernel
theorem bin_t10_F17 : binSols 10 17 = [] := by decide +kernel
theorem bin_t10_F18 : binSols 10 18 = [[6, 2]] := by decide +kernel
theorem bin_t10_F19 : binSols 10 19 = [] := by decide +kernel
theorem bin_t10_F20 : binSols 10 20 = [[10]] := by decide +kernel
theorem bin_t10_F21 : binSols 10 21 = [] := by decide +kernel
theorem bin_t10_F22 : binSols 10 22 = [] := by decide +kernel
theorem bin_t10_F24 : binSols 10 24 = [] := by decide +kernel
theorem bin_t10_F26 : binSols 10 26 = [] := by decide +kernel
theorem bin_t10_F27 : binSols 10 27 = [] := by decide +kernel
theorem bin_t10_F28 : binSols 10 28 = [] := by decide +kernel
theorem bin_t10_F30 : binSols 10 30 = [] := by decide +kernel
theorem bin_t10_F32 : binSols 10 32 = [] := by decide +kernel
theorem bin_t10_F33 : binSols 10 33 = [] := by decide +kernel
theorem bin_t10_F34 : binSols 10 34 = [] := by decide +kernel
theorem bin_t10_F36 : binSols 10 36 = [] := by decide +kernel
theorem bin_t10_F38 : binSols 10 38 = [] := by decide +kernel
theorem bin_t10_F40 : binSols 10 40 = [] := by decide +kernel
theorem bin_t10_F42 : binSols 10 42 = [] := by decide +kernel
theorem bin_t10_F44 : binSols 10 44 = [] := by decide +kernel
theorem bin_t10_F48 : binSols 10 48 = [] := by decide +kernel
theorem bin_t10_F50 : binSols 10 50 = [] := by decide +kernel
theorem bin_t10_F54 : binSols 10 54 = [] := by decide +kernel
theorem bin_t10_F60 : binSols 10 60 = [] := by decide +kernel
theorem bin_t10_F66 : binSols 10 66 = [] := by decide +kernel

/-- Theorem 4.4, t = 11: for every F in the candidate set E_11 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t11_F3 : binSols 11 3 = [] := by decide +kernel
theorem bin_t11_F4 : binSols 11 4 = [] := by decide +kernel
theorem bin_t11_F5 : binSols 11 5 = [] := by decide +kernel
theorem bin_t11_F6 : binSols 11 6 = [] := by decide +kernel
theorem bin_t11_F7 : binSols 11 7 = [] := by decide +kernel
theorem bin_t11_F8 : binSols 11 8 = [] := by decide +kernel
theorem bin_t11_F9 : binSols 11 9 = [] := by decide +kernel
theorem bin_t11_F10 : binSols 11 10 = [] := by decide +kernel
theorem bin_t11_F11 : binSols 11 11 = [] := by decide +kernel
theorem bin_t11_F12 : binSols 11 12 = [] := by decide +kernel
theorem bin_t11_F13 : binSols 11 13 = [] := by decide +kernel
theorem bin_t11_F14 : binSols 11 14 = [] := by decide +kernel
theorem bin_t11_F15 : binSols 11 15 = [] := by decide +kernel
theorem bin_t11_F16 : binSols 11 16 = [] := by decide +kernel
theorem bin_t11_F17 : binSols 11 17 = [] := by decide +kernel
theorem bin_t11_F18 : binSols 11 18 = [[3, 2, 2]] := by decide +kernel
theorem bin_t11_F19 : binSols 11 19 = [] := by decide +kernel
theorem bin_t11_F20 : binSols 11 20 = [[5, 4]] := by decide +kernel
theorem bin_t11_F21 : binSols 11 21 = [[7, 3]] := by decide +kernel
theorem bin_t11_F22 : binSols 11 22 = [[11]] := by decide +kernel
theorem bin_t11_F24 : binSols 11 24 = [[8, 3, 2]] := by decide +kernel
theorem bin_t11_F25 : binSols 11 25 = [] := by decide +kernel
theorem bin_t11_F26 : binSols 11 26 = [[13, 2]] := by decide +kernel
theorem bin_t11_F27 : binSols 11 27 = [] := by decide +kernel
theorem bin_t11_F28 : binSols 11 28 = [] := by decide +kernel
theorem bin_t11_F30 : binSols 11 30 = [[15, 2, 2]] := by decide +kernel
theorem bin_t11_F32 : binSols 11 32 = [] := by decide +kernel
theorem bin_t11_F33 : binSols 11 33 = [] := by decide +kernel
theorem bin_t11_F34 : binSols 11 34 = [] := by decide +kernel
theorem bin_t11_F36 : binSols 11 36 = [] := by decide +kernel
theorem bin_t11_F38 : binSols 11 38 = [] := by decide +kernel
theorem bin_t11_F40 : binSols 11 40 = [] := by decide +kernel
theorem bin_t11_F42 : binSols 11 42 = [] := by decide +kernel
theorem bin_t11_F44 : binSols 11 44 = [] := by decide +kernel
theorem bin_t11_F48 : binSols 11 48 = [] := by decide +kernel
theorem bin_t11_F50 : binSols 11 50 = [] := by decide +kernel
theorem bin_t11_F54 : binSols 11 54 = [] := by decide +kernel
theorem bin_t11_F60 : binSols 11 60 = [] := by decide +kernel
theorem bin_t11_F66 : binSols 11 66 = [] := by decide +kernel

/-- Theorem 4.4, t = 12: for every F in the candidate set E_12 of Theorem 4.3, the complete list of exponent multisets S. -/
theorem bin_t12_F3 : binSols 12 3 = [] := by decide +kernel
theorem bin_t12_F4 : binSols 12 4 = [] := by decide +kernel
theorem bin_t12_F5 : binSols 12 5 = [] := by decide +kernel
theorem bin_t12_F6 : binSols 12 6 = [] := by decide +kernel
theorem bin_t12_F7 : binSols 12 7 = [] := by decide +kernel
theorem bin_t12_F8 : binSols 12 8 = [] := by decide +kernel
theorem bin_t12_F9 : binSols 12 9 = [] := by decide +kernel
theorem bin_t12_F10 : binSols 12 10 = [] := by decide +kernel
theorem bin_t12_F11 : binSols 12 11 = [] := by decide +kernel
theorem bin_t12_F12 : binSols 12 12 = [] := by decide +kernel
theorem bin_t12_F13 : binSols 12 13 = [] := by decide +kernel
theorem bin_t12_F14 : binSols 12 14 = [[2]] := by decide +kernel
theorem bin_t12_F15 : binSols 12 15 = [[3]] := by decide +kernel
theorem bin_t12_F16 : binSols 12 16 = [[4]] := by decide +kernel
theorem bin_t12_F17 : binSols 12 17 = [] := by decide +kernel
theorem bin_t12_F18 : binSols 12 18 = [[6], [2, 2, 2]] := by decide +kernel
theorem bin_t12_F19 : binSols 12 19 = [] := by decide +kernel
theorem bin_t12_F20 : binSols 12 20 = [] := by decide +kernel
theorem bin_t12_F21 : binSols 12 21 = [] := by decide +kernel
theorem bin_t12_F22 : binSols 12 22 = [] := by decide +kernel
theorem bin_t12_F24 : binSols 12 24 = [[12]] := by decide +kernel
theorem bin_t12_F25 : binSols 12 25 = [] := by decide +kernel
theorem bin_t12_F26 : binSols 12 26 = [] := by decide +kernel
theorem bin_t12_F27 : binSols 12 27 = [] := by decide +kernel
theorem bin_t12_F28 : binSols 12 28 = [] := by decide +kernel
theorem bin_t12_F30 : binSols 12 30 = [] := by decide +kernel
theorem bin_t12_F32 : binSols 12 32 = [] := by decide +kernel
theorem bin_t12_F33 : binSols 12 33 = [] := by decide +kernel
theorem bin_t12_F34 : binSols 12 34 = [] := by decide +kernel
theorem bin_t12_F36 : binSols 12 36 = [] := by decide +kernel
theorem bin_t12_F38 : binSols 12 38 = [] := by decide +kernel
theorem bin_t12_F40 : binSols 12 40 = [] := by decide +kernel
theorem bin_t12_F42 : binSols 12 42 = [] := by decide +kernel
theorem bin_t12_F44 : binSols 12 44 = [] := by decide +kernel
theorem bin_t12_F46 : binSols 12 46 = [] := by decide +kernel
theorem bin_t12_F48 : binSols 12 48 = [] := by decide +kernel
theorem bin_t12_F50 : binSols 12 50 = [] := by decide +kernel
theorem bin_t12_F54 : binSols 12 54 = [] := by decide +kernel
theorem bin_t12_F60 : binSols 12 60 = [] := by decide +kernel
theorem bin_t12_F66 : binSols 12 66 = [] := by decide +kernel
theorem bin_t12_F78 : binSols 12 78 = [] := by decide +kernel
theorem bin_t12_F84 : binSols 12 84 = [] := by decide +kernel
theorem bin_t12_F90 : binSols 12 90 = [] := by decide +kernel

/-- Proposition 4.5(b) and Theorem 4.7 on a finite range: for `1 ≤ t ≤ 40`, `1 ≤ c ≤ 7`,
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

/-- Theorem 7.1(a): the five odd Lehmer multisets with at most seven members -/
theorem odd_lehmer :
    (admissible (-1) 2 [(3, 1), (3, 1)] &&
     admissible (-1) 5 [(3, 1), (3, 1), (3, 1), (3, 1)] &&
     admissible (-1) 2 [(5, 1), (5, 1), (3, 2), (3, 2), (89, 1)] &&
     admissible (-1) 4 [(3, 1), (3, 1), (5, 1), (5, 1), (3, 2), (89, 1)] &&
     admissible (-1) 8 [(3, 1), (3, 1), (3, 1), (3, 1), (5, 1), (5, 1), (89, 1)]) = true := by decide +kernel

/-- Theorem 7.1(b): the odd companion multisets with at most six members -/
theorem odd_companion :
    (admissible 1 2 [(3, 1), (5, 1)] &&
     admissible 1 2 [(3, 1), (5, 1), (17, 1)] &&
     admissible 1 2 [(3, 1), (5, 1), (17, 1), (257, 1)] &&
     admissible 1 2 [(5, 1), (5, 1), (5, 1), (43, 1)] &&
     admissible 1 2 [(3, 1), (5, 1), (17, 1), (257, 1), (65537, 1)] &&
     admissible 1 2 [(3, 1), (5, 1), (17, 1), (353, 1), (929, 1)] &&
     admissible 1 2 [(3, 1), (3, 2), (3, 2), (23, 1), (131, 1)] &&
     admissible 1 2 [(3, 1), (5, 1), (17, 1), (353, 1), (929, 1), (83623937, 1)] &&
     admissible 1 2 [(3, 1), (11, 1), (11, 1), (11, 1), (677, 1), (3659, 1)] &&
     admissible 1 2 [(5, 1), (5, 1), (5, 1), (43, 1), (5413, 1), (786349, 1)] &&
     admissible 1 2 [(5, 1), (7, 1), (7, 1), (13, 1), (13, 1), (619, 1)] &&
     admissible 1 4 [(3, 1), (3, 1), (3, 1), (3, 2), (23, 1), (131, 1)]) = true := by decide +kernel

/-- Proposition 7.3: the numbers behind the biquadratic Lehmer ideal in `ℚ(i, √89)`:
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


/-- Proposition 7.5: the companion multiset of mode Q with seven members -/
theorem quad_companion :
    admissible 1 2 [(5, 1), (7, 1), (7, 1), (13, 1), (13, 1), (619, 1), (25629697, 1)] = true := by
  decide +kernel

#print axioms bin_t0_F3
#print axioms bin_t0_F4
#print axioms bin_t0_F5
#print axioms bin_t0_F6
#print axioms bin_t0_F7
#print axioms bin_t0_F8
#print axioms bin_t0_F9
#print axioms bin_t0_F10
#print axioms bin_t0_F12
#print axioms bin_t0_F14
#print axioms bin_t0_F15
#print axioms bin_t0_F16
#print axioms bin_t0_F18
#print axioms bin_t0_F20
#print axioms bin_t0_F24
#print axioms bin_t0_F30
#print axioms bin_t1_F3
#print axioms bin_t1_F4
#print axioms bin_t1_F5
#print axioms bin_t1_F6
#print axioms bin_t1_F7
#print axioms bin_t1_F8
#print axioms bin_t1_F9
#print axioms bin_t1_F10
#print axioms bin_t1_F12
#print axioms bin_t1_F14
#print axioms bin_t1_F15
#print axioms bin_t1_F16
#print axioms bin_t1_F18
#print axioms bin_t1_F20
#print axioms bin_t1_F22
#print axioms bin_t1_F24
#print axioms bin_t1_F30
#print axioms bin_t2_F3
#print axioms bin_t2_F4
#print axioms bin_t2_F5
#print axioms bin_t2_F6
#print axioms bin_t2_F7
#print axioms bin_t2_F8
#print axioms bin_t2_F9
#print axioms bin_t2_F10
#print axioms bin_t2_F12
#print axioms bin_t2_F14
#print axioms bin_t2_F15
#print axioms bin_t2_F16
#print axioms bin_t2_F18
#print axioms bin_t2_F20
#print axioms bin_t2_F22
#print axioms bin_t2_F24
#print axioms bin_t2_F30
#print axioms bin_t2_F36
#print axioms bin_t2_F42
#print axioms bin_t3_F3
#print axioms bin_t3_F4
#print axioms bin_t3_F5
#print axioms bin_t3_F6
#print axioms bin_t3_F7
#print axioms bin_t3_F8
#print axioms bin_t3_F9
#print axioms bin_t3_F10
#print axioms bin_t3_F11
#print axioms bin_t3_F12
#print axioms bin_t3_F14
#print axioms bin_t3_F15
#print axioms bin_t3_F16
#print axioms bin_t3_F18
#print axioms bin_t3_F20
#print axioms bin_t3_F21
#print axioms bin_t3_F22
#print axioms bin_t3_F24
#print axioms bin_t3_F26
#print axioms bin_t3_F28
#print axioms bin_t3_F30
#print axioms bin_t3_F36
#print axioms bin_t3_F42
#print axioms bin_t4_F3
#print axioms bin_t4_F4
#print axioms bin_t4_F5
#print axioms bin_t4_F6
#print axioms bin_t4_F7
#print axioms bin_t4_F8
#print axioms bin_t4_F9
#print axioms bin_t4_F10
#print axioms bin_t4_F11
#print axioms bin_t4_F12
#print axioms bin_t4_F13
#print axioms bin_t4_F14
#print axioms bin_t4_F15
#print axioms bin_t4_F16
#print axioms bin_t4_F18
#print axioms bin_t4_F20
#print axioms bin_t4_F21
#print axioms bin_t4_F22
#print axioms bin_t4_F24
#print axioms bin_t4_F26
#print axioms bin_t4_F28
#print axioms bin_t4_F30
#print axioms bin_t4_F36
#print axioms bin_t4_F42
#print axioms bin_t5_F3
#print axioms bin_t5_F4
#print axioms bin_t5_F5
#print axioms bin_t5_F6
#print axioms bin_t5_F7
#print axioms bin_t5_F8
#print axioms bin_t5_F9
#print axioms bin_t5_F10
#print axioms bin_t5_F11
#print axioms bin_t5_F12
#print axioms bin_t5_F13
#print axioms bin_t5_F14
#print axioms bin_t5_F15
#print axioms bin_t5_F16
#print axioms bin_t5_F18
#print axioms bin_t5_F20
#print axioms bin_t5_F21
#print axioms bin_t5_F22
#print axioms bin_t5_F24
#print axioms bin_t5_F26
#print axioms bin_t5_F28
#print axioms bin_t5_F30
#print axioms bin_t5_F36
#print axioms bin_t5_F42
#print axioms bin_t5_F60
#print axioms bin_t6_F3
#print axioms bin_t6_F4
#print axioms bin_t6_F5
#print axioms bin_t6_F6
#print axioms bin_t6_F7
#print axioms bin_t6_F8
#print axioms bin_t6_F9
#print axioms bin_t6_F10
#print axioms bin_t6_F11
#print axioms bin_t6_F12
#print axioms bin_t6_F13
#print axioms bin_t6_F14
#print axioms bin_t6_F15
#print axioms bin_t6_F16
#print axioms bin_t6_F18
#print axioms bin_t6_F20
#print axioms bin_t6_F21
#print axioms bin_t6_F22
#print axioms bin_t6_F24
#print axioms bin_t6_F26
#print axioms bin_t6_F28
#print axioms bin_t6_F30
#print axioms bin_t6_F32
#print axioms bin_t6_F34
#print axioms bin_t6_F36
#print axioms bin_t6_F40
#print axioms bin_t6_F42
#print axioms bin_t6_F48
#print axioms bin_t6_F60
#print axioms bin_t7_F3
#print axioms bin_t7_F4
#print axioms bin_t7_F5
#print axioms bin_t7_F6
#print axioms bin_t7_F7
#print axioms bin_t7_F8
#print axioms bin_t7_F9
#print axioms bin_t7_F10
#print axioms bin_t7_F11
#print axioms bin_t7_F12
#print axioms bin_t7_F13
#print axioms bin_t7_F14
#print axioms bin_t7_F15
#print axioms bin_t7_F16
#print axioms bin_t7_F18
#print axioms bin_t7_F20
#print axioms bin_t7_F21
#print axioms bin_t7_F22
#print axioms bin_t7_F24
#print axioms bin_t7_F26
#print axioms bin_t7_F28
#print axioms bin_t7_F30
#print axioms bin_t7_F32
#print axioms bin_t7_F34
#print axioms bin_t7_F36
#print axioms bin_t7_F40
#print axioms bin_t7_F42
#print axioms bin_t7_F48
#print axioms bin_t7_F54
#print axioms bin_t7_F60
#print axioms bin_t8_F3
#print axioms bin_t8_F4
#print axioms bin_t8_F5
#print axioms bin_t8_F6
#print axioms bin_t8_F7
#print axioms bin_t8_F8
#print axioms bin_t8_F9
#print axioms bin_t8_F10
#print axioms bin_t8_F11
#print axioms bin_t8_F12
#print axioms bin_t8_F13
#print axioms bin_t8_F14
#print axioms bin_t8_F15
#print axioms bin_t8_F16
#print axioms bin_t8_F17
#print axioms bin_t8_F18
#print axioms bin_t8_F20
#print axioms bin_t8_F21
#print axioms bin_t8_F22
#print axioms bin_t8_F24
#print axioms bin_t8_F26
#print axioms bin_t8_F28
#print axioms bin_t8_F30
#print axioms bin_t8_F32
#print axioms bin_t8_F34
#print axioms bin_t8_F36
#print axioms bin_t8_F38
#print axioms bin_t8_F40
#print axioms bin_t8_F42
#print axioms bin_t8_F48
#print axioms bin_t8_F54
#print axioms bin_t8_F60
#print axioms bin_t9_F3
#print axioms bin_t9_F4
#print axioms bin_t9_F5
#print axioms bin_t9_F6
#print axioms bin_t9_F7
#print axioms bin_t9_F8
#print axioms bin_t9_F9
#print axioms bin_t9_F10
#print axioms bin_t9_F11
#print axioms bin_t9_F12
#print axioms bin_t9_F13
#print axioms bin_t9_F14
#print axioms bin_t9_F15
#print axioms bin_t9_F16
#print axioms bin_t9_F17
#print axioms bin_t9_F18
#print axioms bin_t9_F20
#print axioms bin_t9_F21
#print axioms bin_t9_F22
#print axioms bin_t9_F24
#print axioms bin_t9_F26
#print axioms bin_t9_F27
#print axioms bin_t9_F28
#print axioms bin_t9_F30
#print axioms bin_t9_F32
#print axioms bin_t9_F34
#print axioms bin_t9_F36
#print axioms bin_t9_F38
#print axioms bin_t9_F40
#print axioms bin_t9_F42
#print axioms bin_t9_F48
#print axioms bin_t9_F50
#print axioms bin_t9_F54
#print axioms bin_t9_F60
#print axioms bin_t9_F66
#print axioms bin_t10_F3
#print axioms bin_t10_F4
#print axioms bin_t10_F5
#print axioms bin_t10_F6
#print axioms bin_t10_F7
#print axioms bin_t10_F8
#print axioms bin_t10_F9
#print axioms bin_t10_F10
#print axioms bin_t10_F11
#print axioms bin_t10_F12
#print axioms bin_t10_F13
#print axioms bin_t10_F14
#print axioms bin_t10_F15
#print axioms bin_t10_F16
#print axioms bin_t10_F17
#print axioms bin_t10_F18
#print axioms bin_t10_F19
#print axioms bin_t10_F20
#print axioms bin_t10_F21
#print axioms bin_t10_F22
#print axioms bin_t10_F24
#print axioms bin_t10_F26
#print axioms bin_t10_F27
#print axioms bin_t10_F28
#print axioms bin_t10_F30
#print axioms bin_t10_F32
#print axioms bin_t10_F33
#print axioms bin_t10_F34
#print axioms bin_t10_F36
#print axioms bin_t10_F38
#print axioms bin_t10_F40
#print axioms bin_t10_F42
#print axioms bin_t10_F44
#print axioms bin_t10_F48
#print axioms bin_t10_F50
#print axioms bin_t10_F54
#print axioms bin_t10_F60
#print axioms bin_t10_F66
#print axioms bin_t11_F3
#print axioms bin_t11_F4
#print axioms bin_t11_F5
#print axioms bin_t11_F6
#print axioms bin_t11_F7
#print axioms bin_t11_F8
#print axioms bin_t11_F9
#print axioms bin_t11_F10
#print axioms bin_t11_F11
#print axioms bin_t11_F12
#print axioms bin_t11_F13
#print axioms bin_t11_F14
#print axioms bin_t11_F15
#print axioms bin_t11_F16
#print axioms bin_t11_F17
#print axioms bin_t11_F18
#print axioms bin_t11_F19
#print axioms bin_t11_F20
#print axioms bin_t11_F21
#print axioms bin_t11_F22
#print axioms bin_t11_F24
#print axioms bin_t11_F25
#print axioms bin_t11_F26
#print axioms bin_t11_F27
#print axioms bin_t11_F28
#print axioms bin_t11_F30
#print axioms bin_t11_F32
#print axioms bin_t11_F33
#print axioms bin_t11_F34
#print axioms bin_t11_F36
#print axioms bin_t11_F38
#print axioms bin_t11_F40
#print axioms bin_t11_F42
#print axioms bin_t11_F44
#print axioms bin_t11_F48
#print axioms bin_t11_F50
#print axioms bin_t11_F54
#print axioms bin_t11_F60
#print axioms bin_t11_F66
#print axioms bin_t12_F3
#print axioms bin_t12_F4
#print axioms bin_t12_F5
#print axioms bin_t12_F6
#print axioms bin_t12_F7
#print axioms bin_t12_F8
#print axioms bin_t12_F9
#print axioms bin_t12_F10
#print axioms bin_t12_F11
#print axioms bin_t12_F12
#print axioms bin_t12_F13
#print axioms bin_t12_F14
#print axioms bin_t12_F15
#print axioms bin_t12_F16
#print axioms bin_t12_F17
#print axioms bin_t12_F18
#print axioms bin_t12_F19
#print axioms bin_t12_F20
#print axioms bin_t12_F21
#print axioms bin_t12_F22
#print axioms bin_t12_F24
#print axioms bin_t12_F25
#print axioms bin_t12_F26
#print axioms bin_t12_F27
#print axioms bin_t12_F28
#print axioms bin_t12_F30
#print axioms bin_t12_F32
#print axioms bin_t12_F33
#print axioms bin_t12_F34
#print axioms bin_t12_F36
#print axioms bin_t12_F38
#print axioms bin_t12_F40
#print axioms bin_t12_F42
#print axioms bin_t12_F44
#print axioms bin_t12_F46
#print axioms bin_t12_F48
#print axioms bin_t12_F50
#print axioms bin_t12_F54
#print axioms bin_t12_F60
#print axioms bin_t12_F66
#print axioms bin_t12_F78
#print axioms bin_t12_F84
#print axioms bin_t12_F90
#print axioms bin_three_adic
#print axioms bin_comp_exponent
#print axioms one_p3
#print axioms one_p5
#print axioms one_sols
#print axioms odd_lehmer
#print axioms odd_companion
#print axioms quad_companion
#print axioms biquad
#print axioms quartic_mod2
#print axioms fqx
