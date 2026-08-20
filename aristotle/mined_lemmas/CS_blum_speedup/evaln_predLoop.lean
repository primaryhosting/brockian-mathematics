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


theorem evaln_predLoop (y : ℕ) : ∀ k : ℕ, (y + 2) ^ 4 + y + 2 ≤ k →
    evaln k (Code.prec Code.zero (Code.comp Code.left Code.right)) (Nat.pair 0 y)
      = some (y - 1) := by
  induction y with
  | zero =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    rw [evaln_prec_zero' (show Nat.pair 0 0 ≤ K by rw [show Nat.pair 0 0 = 0 from rfl]; omega),
      evaln_zero' (Nat.zero_le K)]
  | succ y ih =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hKy : (y + 3) ^ 4 + y + 3 ≤ K + 1 := by
      have h : (y + 1 + 2) ^ 4 = (y + 3) ^ 4 := by norm_num
      omega
    have hmono : (y + 2) ^ 4 ≤ (y + 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have hguard : Nat.pair 0 (y + 1) ≤ K := by
      have h1 : Nat.pair 0 (y + 1) < (y + 2) ^ 2 := by simpa using pair_lt_sq 0 (y + 1)
      have h2 : (y + 2) ^ 2 ≤ (y + 3) ^ 4 := by nlinarith [sq_nonneg y]
      omega
    rw [evaln_prec_succ' hguard, ih K (by omega)]
    simp only [Option.bind_some]
    have hz : Nat.pair y (y - 1) < (y + 1) ^ 2 := by
      have hm : max y (y - 1) = y := by omega
      simpa [hm] using pair_lt_sq y (y - 1)
    have hzK : Nat.pair y (y - 1) ≤ K := by
      have h2 : (y + 1) ^ 2 ≤ (y + 3) ^ 4 := by nlinarith [sq_nonneg y]
      omega
    have hv : Nat.pair 0 (Nat.pair y (y - 1)) < (y + 1) ^ 4 := by
      have hm : max y (y - 1) = y := by omega
      simpa [hm] using pair_pair_bound y (y - 1)
    have hvK : Nat.pair 0 (Nat.pair y (y - 1)) ≤ K := by
      have h : (y + 1) ^ 4 ≤ (y + 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    rw [evaln_comp' hvK, evaln_right' hvK]
    simp only [Nat.unpair_pair, Option.bind_some]
    rw [evaln_left' hzK]
    simp

