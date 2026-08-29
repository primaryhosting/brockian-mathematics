import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma critVal_eq_coe_critValFinset (f : ℚ[X]) (hf : derivative f ≠ 0) :
    critVal f = (critValFinset f : Set ℂ) := by
  have hmap : (derivative f).map (algebraMap ℚ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hf
  ext v
  simp only [critVal, critValFinset, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hmap, Polynomial.IsRoot,
    Polynomial.eval_map, ← Polynomial.aeval_def]

