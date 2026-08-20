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

namespace Frontier

/-- The "Mexican hat" scalar potential of the abelian Higgs toy model,
`V(φ) = lam * (‖φ‖² - v²)²`, for a complex scalar field value `φ`. -/

noncomputable def gaugeBosonMassSq (g : ℝ) (phi : ℂ) : ℝ :=
  g ^ 2 * ‖phi‖ ^ 2

/-- **Spontaneous symmetry breaking gives the gauge boson a mass** (abelian Higgs toy model).

For a Mexican-hat potential `V(φ) = lam (‖φ‖² - v²)²` with `lam > 0` and `v > 0`:

* `V` is nonnegative, so its vacua are exactly its zeros;
* the vacua are exactly the field values on the circle `‖φ‖ = v`, i.e. the symmetric
  point `φ = 0` is *not* a vacuum;
* at every vacuum the gauge boson mass squared equals `g² v²`, which is strictly positive
  for `g ≠ 0`;
* at the symmetric (unbroken) point `φ = 0` the gauge boson is massless.
-/
