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

lemma sum_coeff_mul_chi {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (∑ S : Finset (Fin n), fourierCoeff f S * chi S x)
      = 2 ^ n * (if f x then (-1 : ℤ) else 1) := by
  have hswap : (∑ S : Finset (Fin n), fourierCoeff f S * chi S x)
      = ∑ y : Fin n → Bool, (if f y then (-1 : ℤ) else 1) *
          (∑ S : Finset (Fin n), chi S y * chi S x) := by
    simp only [fourierCoeff, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hswap]
  simp only [sum_chi_mul_chi]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- A Fourier coefficient at a set containing a coordinate that `f` does not depend on
vanishes. -/
