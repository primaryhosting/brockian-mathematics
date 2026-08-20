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

lemma exists_subset_sum_le {m : Type*} (a : m → ℝ) (eps : ℝ) (heps : ∀ i, a i ≤ eps)
    (t : ℝ) (ht : 0 ≤ t) (F : Finset m) :
    ∃ S ⊆ F, ∑ i ∈ S, a i ≤ t ∧ (S = F ∨ t - eps ≤ ∑ i ∈ S, a i) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simpa using ht, Or.inl rfl⟩
  | insert x F hx ih =>
      obtain ⟨S, hSF, hSle, hcase⟩ := ih
      rcases hcase with rfl | hlow
      · by_cases hle : ∑ i ∈ insert x S, a i ≤ t
        · exact ⟨insert x S, by simp, hle, Or.inl rfl⟩
        · refine ⟨S, hSF.trans (Finset.subset_insert _ _), hSle, Or.inr ?_⟩
          push_neg at hle
          rw [Finset.sum_insert hx] at hle
          have := heps x
          linarith
      · exact ⟨S, hSF.trans (Finset.subset_insert _ _), hSle, Or.inr hlow⟩

