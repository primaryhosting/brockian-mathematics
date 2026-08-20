import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/

private lemma sum_shift (p : ℕ) [Fact p.Prime] (hp : Odd p) (m : ZMod p) :
    ∑ l : ZMod p, (ZMod.stdAddChar (2 * m * l) : ℂ) = if m = 0 then (p : ℂ) else 0 := by
  classical
  have key := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) (2 * m)
    (ZMod.isPrimitive_stdAddChar p)
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hcomm : ∀ l : ZMod p, l * (2 * m) = 2 * m * l := fun l => mul_comm _ _
  simp_rw [hcomm] at key
  by_cases hm : m = 0
  · rw [key, hcard, if_pos (by simp [hm]), if_pos hm]
  · have h2m : 2 * m ≠ 0 := fun h => hm ((two_mul_eq_zero_iff p hp m).mp h)
    rw [key, if_neg h2m, if_neg hm, Nat.cast_zero]

/-- Expanding `S * conj S` and reindexing `k = l + m`. -/
