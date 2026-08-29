/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma coeff_eq_zero_of_invariant {n : ℕ} {f : (Fin n → Bool) → Bool} {k : Fin n}
    (hinv : ∀ x, f (flipAt x k) = f x) {S : Finset (Fin n)} (hk : k ∈ S) :
    fourierCoeff f S = 0 := by
  have hbij : (∑ x : Fin n → Bool, (if f x then (-1 : ℤ) else 1) * chi S x)
      = ∑ x : Fin n → Bool, (if f (flipAt x k) then (-1 : ℤ) else 1) * chi S (flipAt x k) := by
    refine (Fintype.sum_equiv (Function.Involutive.toPerm (fun x => flipAt x k)
      (fun x => flipAt_flipAt x k)) _ _ ?_).symm
    intro x
    rfl
  have hneg : fourierCoeff f S = - fourierCoeff f S := by
    conv_lhs => rw [fourierCoeff, hbij]
    simp only [hinv, chi_flipAt_of_mem hk, mul_neg, Finset.sum_neg_distrib]
    rw [fourierCoeff]
  linarith

/-! ## Degree zero and sensitivity zero both characterize constant functions -/

