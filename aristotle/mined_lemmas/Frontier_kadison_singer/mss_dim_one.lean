/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace Frontier
namespace KadisonSinger

/-! ## The setting

Let `H` be a complex Hilbert space with a distinguished orthonormal (Hilbert) basis `e : ι → H`.
The *diagonal* subalgebra `𝒟` (an atomic MASA in `B(H)`, isomorphic to `ℓ^∞(ι)`) consists of the
bounded operators that are diagonalised by the basis.  The Kadison–Singer problem asks whether
every pure state of `𝒟` extends *uniquely* to a state of `B(H)`; this was answered
affirmatively by Marcus, Spielman and Srivastava.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`, i.e. `u u*`. -/

theorem mss_dim_one : MSS 1 := by
  intro m _ _ v eps hsmall hres
  set a : m → ℝ := fun i => ‖v i 0‖ ^ 2 with ha
  have ha_nonneg : ∀ i, 0 ≤ a i := fun i => by positivity
  have ha_le : ∀ i, a i ≤ eps := by
    intro i
    have := hsmall i
    simpa [ha, Fin.sum_univ_one] using this
  have htot : ∑ i, a i = 1 := by
    have h := congrArg (fun M => M 0 0) hres
    simp only [Matrix.sum_apply, outer_apply_zero_zero, Matrix.one_apply_eq] at h
    have h' : ((∑ i, a i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; simpa [ha] using h
    exact_mod_cast h'
  have hm : Nonempty m := by
    by_contra hempty
    simp [not_nonempty_iff.mp (not_nonempty_iff.mpr (by simpa using hempty))] at htot
  have heps_nonneg : 0 ≤ eps := le_trans (ha_nonneg (Classical.arbitrary m))
    (ha_le (Classical.arbitrary m))
  obtain ⟨S, -, hSle, hcase⟩ := exists_subset_sum_le a eps ha_le (1 / 2) (by norm_num)
    (Finset.univ : Finset m)
  have hlow : 1 / 2 - eps ≤ ∑ i ∈ S, a i := by
    rcases hcase with rfl | h
    · rw [htot] at hSle; linarith
    · exact h
  have hcompl : ∑ i ∈ Sᶜ, a i ≤ 1 / 2 + eps := by
    have hsplit : ∑ i ∈ S, a i + ∑ i ∈ Sᶜ, a i = 1 := by
      rw [← htot]
      exact Finset.sum_add_sum_compl S a
    linarith
  have hc : 1 / 2 + eps ≤ (1 / Real.sqrt 2 + Real.sqrt eps) ^ 2 := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have he : (Real.sqrt eps) ^ 2 = eps := Real.sq_sqrt heps_nonneg
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hse : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg eps
    have hexp : (1 / Real.sqrt 2 + Real.sqrt eps) ^ 2
        = 1 / 2 + eps + 2 * (1 / Real.sqrt 2) * Real.sqrt eps := by
      field_simp
      nlinarith [h2, he, hs2.le]
    rw [hexp]
    have : 0 ≤ 2 * (1 / Real.sqrt 2) * Real.sqrt eps := by positivity
    linarith
  refine ⟨S, boundedBy_of_le v S _ ?_, boundedBy_of_le v Sᶜ _ ?_⟩
  · exact le_trans hSle (by linarith)
  · exact le_trans hcompl hc

end Weaver

end Frontier

