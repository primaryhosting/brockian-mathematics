import Mathlib
/-!
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module docstrings, so the required header is placed immediately after the import.

namespace Math

/-- **Baire category theorem.** A nonempty complete metric space is not a countable union
of nowhere dense sets. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (s : ℕ → Set X) (hs : ∀ n, IsNowhereDense (s n)) :
    (⋃ n, s n) ≠ Set.univ := by
  intro hcov
  -- The complements of the closures are open and dense.
  have hopen : ∀ n, IsOpen (closure (s n))ᶜ := fun n => isClosed_closure.isOpen_compl
  have hdense : ∀ n, Dense (closure (s n))ᶜ := by
    intro n
    have h := hs n
    rw [IsNowhereDense, interior_eq_empty_iff_dense_compl] at h
    exact h
  have hInter : Dense (⋂ n, (closure (s n))ᶜ) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨x, hx⟩ := hInter.nonempty
  have hx' : x ∈ ⋃ n, s n := by rw [hcov]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx'
  exact (Set.mem_iInter.mp hx n) (subset_closure hn)

end Math

import Mathlib

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

