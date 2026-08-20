/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; its text is otherwise verbatim.)

import Mathlib

/-!
We work with Mathlib's model of computation `Nat.Partrec.Code` together with its canonical
step-indexed evaluator `Nat.Partrec.Code.evaln`.  The running time of a program `c` on input `x`
is the least step bound `k` for which `evaln k c x` returns a value.

We exhibit an explicit total computable function `gfun` (a doubly exponentially growing function)
with *no fastest program*: for every program `c` computing `gfun` there is another program `d`
computing `gfun` which is strictly faster on all but finitely many inputs.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Elementary arithmetic helpers -/


theorem speedup_core {c : Code} (hc : eval c = fun x => Part.some (gfun x)) :
    ∀ x, 2 * (cdepth c + 8) + 60 ≤ x →
      timeOf (fastCode (cdepth c + 8)) x ^ 3 ≤ timeOf c x ∧
        timeOf (fastCode (cdepth c + 8)) x < timeOf c x := by
  intro x hx
  set d := cdepth c with hd
  set A := (2 : ℕ) ^ 2 ^ (x - d - 3) with hA
  -- upper bound for the fast program
  have hup : timeOf (fastCode (d + 8)) x ≤ A := by
    have h1 : timeOf (fastCode (d + 8)) x ≤ bud (d + 8) x := timeOf_fastCode_le _ _
    have h2 : bud (d + 8) x ≤ 2 ^ 2 ^ (x - (d + 8) + 5) := bud_le_tower _ _ (by omega)
    have h3 : x - (d + 8) + 5 = x - d - 3 := by omega
    rw [h3] at h2
    omega
  -- lower bound for an arbitrary program computing `gfun`
  have hlow : 2 ^ 2 ^ (x - 1 - d) ≤ timeOf c x + 2 := timeOf_lower_bound hc x (by omega)
  have hexp : (2 : ℕ) ^ 2 ^ (x - 1 - d) = A ^ 4 := by
    rw [hA, ← pow_mul]
    congr 1
    rw [show x - 1 - d = (x - d - 3) + 2 by omega, pow_add]
    ring
  rw [hexp] at hlow
  have hA2 : 2 ≤ A := by
    rw [hA]
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 2 ^ (x - d - 3) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hA3 : 8 ≤ A ^ 3 := by simpa using Nat.pow_le_pow_left hA2 3
  have hcube : A ^ 3 + 2 ≤ A ^ 4 :=
    calc A ^ 3 + 2 ≤ A ^ 3 + A ^ 3 := by omega
      _ = 2 * A ^ 3 := by ring
      _ ≤ A * A ^ 3 := Nat.mul_le_mul_right _ hA2
      _ = A ^ 4 := by ring
  have hlin : A + 3 ≤ A ^ 3 :=
    calc A + 3 ≤ A * 4 := by omega
      _ ≤ A * A ^ 2 := Nat.mul_le_mul_left A (by simpa using Nat.pow_le_pow_left hA2 2)
      _ = A ^ 3 := by ring
  have hfast : timeOf (fastCode (d + 8)) x ^ 3 ≤ A ^ 3 := Nat.pow_le_pow_left hup 3
  exact ⟨by omega, by omega⟩

/-- **Blum speedup**: there is a problem with no fastest algorithm.  Concretely, there is a total
computable function `f` (namely `gfun`) such that every program `c` computing `f` is beaten, on
all but finitely many inputs, by another program `d` computing `f`. -/
