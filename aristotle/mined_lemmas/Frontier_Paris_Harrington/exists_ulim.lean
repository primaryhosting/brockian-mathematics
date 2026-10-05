import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/

theorem exists_ulim {r : ℕ} (U : Ultrafilter ℕ) (f : ℕ → Fin r) :
    ∃ j : Fin r, {x | f x = j} ∈ U := by
  have h : (⋃ j ∈ (Set.univ : Set (Fin r)), {x | f x = j}) ∈ U := by
    have hu : (⋃ j ∈ (Set.univ : Set (Fin r)), {x | f x = j}) = Set.univ := by
      ext x; simp
    rw [hu]; exact Filter.univ_mem
  obtain ⟨j, -, hj⟩ := (Ultrafilter.finite_biUnion_mem_iff Set.finite_univ).1 h
  exact ⟨j, hj⟩

/-- The `U`-limit of a function with values in a finite type. -/
