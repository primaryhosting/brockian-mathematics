/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

lemma hypercube_adj_iff_card_eq_one {k : ℕ} (x y : Fin k → Bool) :
    (hypercube k).Adj x y ↔ (Finset.univ.filter (fun i : Fin k => x i ≠ y i)).card = 1 := by
  constructor
  · rintro ⟨i, rfl⟩
    have : Finset.univ.filter (fun i' : Fin k => x i' ≠ cflip i x i') = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj
        by_contra hji
        exact hj (by rw [cflip_of_ne hji])
      · rintro rfl
        simp
    rw [this, Finset.card_singleton]
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h
    refine ⟨i, funext fun j => ?_⟩
    rcases eq_or_ne j i with rfl | hji
    · have hj : j ∈ ({j} : Finset (Fin k)) := Finset.mem_singleton_self j
      rw [← hi] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [cflip_self]
      revert hj
      cases x j <;> cases y j <;> simp
    · have hj : j ∉ ({i} : Finset (Fin k)) := by simpa using hji
      rw [← hi] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      rw [cflip_of_ne hji, hj]

/-- `Q_k` has `2 ^ k` vertices. -/
