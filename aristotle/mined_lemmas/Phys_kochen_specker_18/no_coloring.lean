import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- Integer coordinates of the 18 vectors of the Cabello–Estebaranz–García-Alcaine
Kochen–Specker set in `ℝ⁴`. -/

lemma no_coloring :
    ¬ ∃ f : Fin 18 → ℕ, (∀ i, f i ≤ 1) ∧ ∀ j : Fin 9, ∑ i ∈ ksBasis j, f i = 1 := by
  rintro ⟨f, -, hf⟩
  have h1 : ∑ j : Fin 9, ∑ i ∈ ksBasis j, f i = 9 := by
    simp [hf]
  have h2 : ∑ j : Fin 9, ∑ i ∈ ksBasis j, f i
      = ∑ j : Fin 9, ∑ i : Fin 18, (if i ∈ ksBasis j then f i else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h3 : ∀ i : Fin 18, ∑ j : Fin 9, (if i ∈ ksBasis j then f i else 0) = 2 * f i := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, ksBasis_count i, smul_eq_mul]
  rw [h2, Finset.sum_comm] at h1
  simp only [h3] at h1
  rw [← Finset.mul_sum] at h1
  omega

/-- **Kochen–Specker theorem, 18-vector version.**
The 18 explicit vectors `ksVec` in `ℝ⁴` are nonzero and pairwise distinct, the nine index
sets `ksBasis` each consist of four indices whose vectors are pairwise orthogonal (hence
form an orthogonal basis of `ℝ⁴`), and yet there is no `{0,1}`-valued coloring of the
18 vectors assigning the value `1` to exactly one vector in each of the nine bases. -/
