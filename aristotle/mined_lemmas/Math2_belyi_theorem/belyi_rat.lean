import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyi_rat (T : Finset ℚ) : BelyiFor ((fun q : ℚ => (q : ℂ)) '' (T : Set ℚ)) := by
  classical
  set M : ℚ := ∑ t ∈ T, |t| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun t _ => abs_nonneg t
  have hden : (0 : ℚ) < 2 * M + 1 := by linarith
  set L : ℚ[X] := C (2 * M + 1)⁻¹ * (X + C M) with hL
  have hLeval : ∀ t : ℚ, L.eval t = (t + M) / (2 * M + 1) := by
    intro t; simp [hL, div_eq_inv_mul]
  have hLdeg : 0 < L.natDegree := by
    have hc : (2 * M + 1)⁻¹ ≠ 0 := by positivity
    rw [hL, natDegree_C_mul hc]
    have : ((X : ℚ[X]) + C M).natDegree = 1 := by compute_degree!
    omega
  set T' : Finset ℚ := T.image (fun t => L.eval t) with hT'
  have hT'mem : ∀ t ∈ T', 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    rw [hT', Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have habs : |u| ≤ M := Finset.single_le_sum (f := fun t => |t|) (fun i _ => abs_nonneg i) hu
    have h1 : -M ≤ u := neg_le_of_abs_le habs
    have h2 : u ≤ M := le_of_abs_le habs
    rw [hLeval]
    exact ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one hden]; linarith⟩
  refine belyi_comp L hLdeg _ _ ?_ ?_ (belyi_rat_Icc T'.card T' hT'mem (Finset.card_filter_le _ _))
  · intro z hz
    exfalso
    rw [hL] at hz
    simp only [derivative_mul, derivative_C, derivative_X, zero_mul, add_zero, zero_add,
      mul_one, map_add, aeval_C] at hz
    have hne : ((2 * M + 1)⁻¹ : ℚ) ≠ 0 := by positivity
    have hcast : (((2 * M + 1)⁻¹ : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hne
    exact hcast (by simpa using hz)
  · rintro s ⟨t, ht, rfl⟩
    exact ⟨L.eval t, by rw [hT']; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ht),
      (aeval_rat L t).symm ▸ rfl⟩

/-! ### Descent on the degree -/

