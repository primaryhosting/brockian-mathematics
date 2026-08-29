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

theorem cxStructure_inl (v : SymplecticSpace ι) (i : ι) :
    (cxStructure v) (Sum.inl i) = v (Sum.inr i) := by
  simp [cxStructure]

@[simp]
