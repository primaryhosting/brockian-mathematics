/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Combinatorial (Levitt–Knill) Chern–Gauss–Bonnet

The smooth Chern–Gauss–Bonnet theorem states that for a closed oriented Riemannian
manifold `M` of even dimension `2n`,
`χ(M) = (2π)⁻ⁿ ∫_M Pf(Ω)`, where `Pf(Ω)` is the Pfaffian of the curvature `2`-form.
Mathlib currently has no Riemannian curvature tensor, no Pfaffian of a curvature form and
no integration of differential forms over manifolds, so that analytic statement cannot even
be *written* here, let alone proved.

What is developed and proved below is the **combinatorial Gauss–Bonnet theorem**
(Levitt, Knill): the discrete analogue of Chern–Gauss–Bonnet, in which the Pfaffian
curvature density is replaced by the *combinatorial curvature* of a vertex of a finite
simplicial complex, and the integral by a finite sum over vertices.  The total curvature
equals the Euler characteristic.  Together with it we prove the classical
**angle–defect Gauss–Bonnet theorem** for closed triangulated surfaces:
the total angle defect equals `2π` times the Euler characteristic.
-/

namespace Math2

open Finset

variable {V : Type*} [DecidableEq V]

/-- The vertex set of a finite family of simplices `K`. -/

def IsPure (K : Finset (Finset V)) (d : ℕ) : Prop :=
  (∀ S ∈ K, S.card ≤ d + 1) ∧ ∀ S ∈ K, ∃ T ∈ K, S ⊆ T ∧ T.card = d + 1

/-- `K` is closed (without boundary) in dimension `d`: every codimension-one face lies in
exactly two `d`-dimensional simplices. -/
