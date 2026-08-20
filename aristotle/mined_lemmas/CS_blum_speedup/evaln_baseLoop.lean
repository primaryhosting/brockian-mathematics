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


theorem evaln_baseLoop (y : ℕ) : ∀ k : ℕ, (gfun y + 2) ^ 4 + y + 2 ≤ k →
    evaln k (Code.prec oneCode baseBody) (Nat.pair 0 y) = some (gfun y) := by
  induction y with
  | zero =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    rw [evaln_prec_zero' (show Nat.pair 0 0 ≤ K by rw [show Nat.pair 0 0 = 0 from rfl]; omega),
      evaln_oneCode (Nat.zero_le K)]
    rfl
  | succ y ih =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hgy : gfun y ≤ gfun (y + 1) := gfun_le_succ y
    have hy1 : y + 1 ≤ gfun (y + 1) := self_le_gfun (y + 1)
    have hK : (gfun (y + 1) + 2) ^ 4 + y + 3 ≤ K + 1 := by
      have h : (gfun (y + 1) + 2) ^ 4 + (y + 1) + 2 ≤ K + 1 := hk
      omega
    have hGmono : (gfun y + 2) ^ 4 ≤ (gfun (y + 1) + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have hsq : ∀ t : ℕ, t ≤ gfun (y + 1) + 2 → t ^ 2 ≤ (gfun (y + 1) + 2) ^ 4 := by
      intro t ht
      calc t ^ 2 ≤ (gfun (y + 1) + 2) ^ 2 := Nat.pow_le_pow_left ht 2
        _ ≤ (gfun (y + 1) + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hguard : Nat.pair 0 (y + 1) ≤ K := by
      have h1 : Nat.pair 0 (y + 1) < (y + 2) ^ 2 := by simpa using pair_lt_sq 0 (y + 1)
      have h2 := hsq (y + 2) (by omega)
      omega
    rw [evaln_prec_succ' hguard, ih K (by omega)]
    simp only [Option.bind_some]
    have hm : max y (gfun y) = gfun y := by have := self_le_gfun y; omega
    have hz : Nat.pair y (gfun y) < (gfun y + 1) ^ 2 := by simpa [hm] using pair_lt_sq y (gfun y)
    have hzK : Nat.pair y (gfun y) ≤ K := by
      have h2 := hsq (gfun y + 1) (by omega)
      omega
    have hv : Nat.pair 0 (Nat.pair y (gfun y)) < (gfun y + 1) ^ 4 := by
      simpa [hm] using pair_pair_bound y (gfun y)
    have hvK : Nat.pair 0 (Nat.pair y (gfun y)) ≤ K := by
      have h : (gfun y + 1) ^ 4 ≤ (gfun (y + 1) + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    rw [evaln_baseBody hvK hzK (by omega)]
    rfl

