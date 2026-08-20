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

/-! ### An abelian Higgs toy model

We model a `U(1)` gauge theory coupled to a complex scalar `φ` with charge `q`.
Everything is reduced to its algebraic content:

* the scalar potential only depends on the modulus `r = ‖φ‖` and is the standard
  "mexican hat" `V(r) = lam * (r ^ 2 - v ^ 2) ^ 2`;
* the gauge field enters through the covariant derivative `D φ = dφ - i q A φ`;
* a constant scalar background of modulus `r` therefore contributes a term
  `q ^ 2 * r ^ 2 * A ^ 2` to `‖D φ‖ ^ 2`, i.e. a mass term for `A` with
  mass squared `q ^ 2 * r ^ 2`.

Spontaneous symmetry breaking is the statement that the potential is minimised at
`r = v ≠ 0` rather than at the symmetric point `r = 0`, and hence that the gauge
boson acquires a strictly positive mass `|q| * v`. -/

/-- The Higgs ("mexican hat") potential, as a function of the modulus `r = ‖φ‖`. -/

noncomputable def gaugeMassSq (q r : ℝ) : ℝ := q ^ 2 * r ^ 2

/-- For a constant scalar background of modulus `r`, the covariant kinetic term
`‖D φ‖ ^ 2` is exactly the mass term `gaugeMassSq q r * A ^ 2` for the gauge field. -/
