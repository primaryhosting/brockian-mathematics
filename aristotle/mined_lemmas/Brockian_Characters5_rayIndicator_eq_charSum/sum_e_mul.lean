/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `a ↦ ω ^ a.val` on `ZMod 5`. -/

lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hb : b = 0
  · subst hb
    simp only [zero_mul, e]
    norm_num
  · rw [if_neg hb]
    have h : ∑ a : ZMod 5, e (b * a) = ∑ a : ZMod 5, e a :=
      Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ (fun _ => rfl)
    rw [h]
    show (∑ a : Fin 5, ω ^ (a : ℕ)) = 0
    rw [Fin.sum_univ_five]
    norm_num
    linear_combination sum_omega_pow

/-- The indicator of the ray `n ≡ r (mod 5)`. -/
