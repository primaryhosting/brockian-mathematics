import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

namespace Frontier

open Finset
open scoped Matrix

/-! ## The Boolean hypercube -/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a hypercube vertex. -/

lemma hcount_flipAt_lt_of_true (x : Cube n) {i k : Fin n} (h : i < k) (hk : x k = true) :
    hcount x i = hcount (flipAt x k) i + 1 := by
  unfold hcount
  have hmem : k ∉ ({j ∈ Finset.univ | i < j ∧ flipAt x k j = true} : Finset (Fin n)) := by
    simp [hk]
  have hset : ({j ∈ Finset.univ | i < j ∧ x j = true} : Finset (Fin n))
      = insert k ({j ∈ Finset.univ | i < j ∧ flipAt x k j = true} : Finset (Fin n)) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hjk : j = k
      · exact Or.inl hjk
      · exact Or.inr ⟨h1, by rwa [flipAt_of_ne _ hjk]⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨h, hk⟩
      · by_cases hjk : j = k
        · subst hjk; simp [hk] at h2
        · rw [flipAt_of_ne _ hjk] at h2; exact ⟨h1, h2⟩
  rw [hset, Finset.card_insert_of_notMem hmem]

