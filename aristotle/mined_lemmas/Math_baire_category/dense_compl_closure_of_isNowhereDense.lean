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
