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

/-
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- A *Landau prime* is a prime of the form `n ^ 2 + 1`. -/

lemma landauArguments_finite_of_finite
    (h : {p : ℕ | IsLandauPrime p}.Finite) : LandauArguments.Finite := by
  apply Set.Finite.of_finite_image (f := fun n : ℕ => n ^ 2 + 1)
  · refine h.subset ?_
    rintro p ⟨n, hn, rfl⟩
    exact ⟨hn, n, rfl⟩
  · intro a _ b _ hab
    have hab2 : a ^ 2 = b ^ 2 := by simpa using hab
    exact Nat.pow_left_injective (by norm_num) hab2

