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

namespace Math

/-- **Baire category theorem.**  A nonempty complete metric space is not the union of a
countable family of nowhere dense sets: if every `f n` has closure with empty interior,
then `⋃ n, f n` cannot be all of `X`. -/

theorem baire_category' {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] (f : ι → Set X)
    (hf : ∀ i, IsNowhereDense (f i)) :
    (⋃ i, f i) ≠ Set.univ :=
  baire_category f hf

end Math

