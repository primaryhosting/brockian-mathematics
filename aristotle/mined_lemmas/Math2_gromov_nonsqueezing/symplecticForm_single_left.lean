/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

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

namespace Math2

/-- The symplectic vector space `ℝ^{2n}`, modelled as the Euclidean space indexed by `ι ⊕ ι`:
the `Sum.inl` coordinates are the "positions" and the `Sum.inr` coordinates the "momenta". -/
abbrev SymplecticSpace (ι : Type*) [Fintype ι] : Type _ := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form on `ℝ^{2n} = ℝ^ι × ℝ^ι`,
`ω(u, v) = ∑ i, (u_i v_{n+i} - u_{n+i} v_i)`. -/

theorem symplecticForm_single_left [DecidableEq ι] (u : SymplecticSpace ι) (i : ι) :
    symplecticForm (EuclideanSpace.single (Sum.inl i) (1 : ℝ)) u = u (Sum.inr i) := by
  simp [symplecticForm, EuclideanSpace.single_apply]

/-- **Linear Gromov nonsqueezing.**

If a linear symplectomorphism `Φ` of the standard symplectic vector space `ℝ^{2n}` maps the
open ball of radius `r` around the origin into the open symplectic cylinder
`Z(R) = {v | v_{i₀}² + v_{n+i₀}² < R²}`, then `r ≤ R`.

(This is the linear case of Gromov's nonsqueezing theorem: no symplectic linear map can squeeze
a ball into a thinner symplectic cylinder, even though maps of arbitrarily large distortion
preserving volume exist.) -/
