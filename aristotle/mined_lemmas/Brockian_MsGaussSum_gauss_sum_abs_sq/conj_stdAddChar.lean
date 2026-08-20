import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/

private lemma conj_stdAddChar (p : ℕ) [NeZero p] [Fact p.Prime] (x : ZMod p) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  simp [ZMod.stdAddChar, ZMod.toCircle, AddCircle.toCircle_addChar]
  -- goal: (starRingEnd ℂ) ↑(ZMod.toAddCircle x).toCircle = ↑(-ZMod.toAddCircle x).toCircle
  trans (↑(AddCircle.toCircle (ZMod.toAddCircle x)))⁻¹
  · -- Use that conj(z) = z⁻¹ for |z| = 1
    have hnorm : ‖(AddCircle.toCircle (ZMod.toAddCircle x) : ℂ)‖ = 1 := by simp
    -- conj(z) = z⁻¹ for |z| = 1
    have h1 : (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ) * (starRingEnd ℂ) (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have h2 : (starRingEnd ℂ) (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ) = (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h1
    exact h2
  · rw [AddCircle.toCircle_neg]
    rfl

/-- For an odd prime `p`, multiplication by `2` is injective on `ZMod p`. -/
