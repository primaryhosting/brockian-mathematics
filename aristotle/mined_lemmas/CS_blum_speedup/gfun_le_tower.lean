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


theorem gfun_le_tower (y : ℕ) : gfun y + 3 ≤ 2 ^ 2 ^ (y + 2) := by
  induction y with
  | zero => decide
  | succ n ih =>
    set A := 2 ^ 2 ^ (n + 2) with hA
    have hA2 : 2 ≤ A := by
      have h : (2:ℕ) ^ 1 ≤ 2 ^ 2 ^ (n + 2) :=
        Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
      simpa using h
    have h1 : Nat.pair (n + 1) (gfun n) < (max (n + 1) (gfun n) + 1) ^ 2 := pair_lt_sq _ _
    have h2 : max (n + 1) (gfun n) ≤ gfun n + 1 := by
      have := self_le_gfun n; omega
    have h3 : Nat.pair (n + 1) (gfun n) < (gfun n + 2) ^ 2 :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_left (by omega) 2)
    have h4 : (gfun n + 2) ^ 2 ≤ (A - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h5 : 2 ^ 2 ^ (n + 3) = A * A := by rw [hA, ← pow_add]; ring_nf
    have h6 : (A - 1) ^ 2 + 2 ≤ A * A := by
      have h' : (A - 1) ^ 2 = (A - 1) * (A - 1) := by ring
      have h'' : A - 1 + 1 = A := by omega
      nlinarith [hA2, h'']
    have h7 : gfun (n + 1) + 3 ≤ A * A := by simp only [gfun]; omega
    rw [show n + 1 + 2 = n + 3 from rfl, h5]; exact h7

/-! ### Unfolding lemmas for `evaln` -/

