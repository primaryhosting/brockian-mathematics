/-
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
/-!
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module docstring `/-! ... -/`, so the requested
header appears at the very top of the file as a plain block comment and is repeated here
verbatim as the module docstring.)
-/

namespace Math

open Set

/-- The complement of the closure of a nowhere dense set is dense. -/
theorem dense_compl_closure_of_isNowhereDense {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsNowhereDense s) : Dense ((closure s)ᶜ) :=
  interior_eq_empty_iff_dense_compl.mp hs

/-- **Baire category theorem**: a nonempty complete metric space is not the union of
countably many nowhere dense sets. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (s : ℕ → Set X) (hs : ∀ n, IsNowhereDense (s n)) : ⋃ n, s n ≠ (univ : Set X) := by
  intro hcov
  have hdense : Dense (⋂ n, (closure (s n))ᶜ) :=
    dense_iInter_of_isOpen (fun n => isClosed_closure.isOpen_compl)
      (fun n => dense_compl_closure_of_isNowhereDense (hs n))
  obtain ⟨x, hx⟩ := hdense.nonempty
  have hxu : x ∈ ⋃ n, s n := by rw [hcov]; trivial
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxu
  exact (mem_iInter.mp hx n) (subset_closure hn)

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

