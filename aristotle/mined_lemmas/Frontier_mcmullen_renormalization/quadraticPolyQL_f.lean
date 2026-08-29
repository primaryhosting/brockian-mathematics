/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a holomorphic map `f : U → V` between bounded open subsets of `ℂ`
with `U ⋐ V`, which is a proper degree-two branched covering onto `V`.

We encode "proper degree two branched covering" concretely and checkably:
`f` maps `U` into `V`, `f` is onto `V`, every fibre over `V` has at most two points,
and `f` has a unique critical point in `U`.
-/

/-- A quadratic-like map: a holomorphic degree-two proper map `f : U → V` with
`closure U ⊆ V` and `U` bounded. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  /-- `U ⋐ V` : the closure of `U` is contained in `V`. -/
  closure_subset : closure U ⊆ V
  bounded_U : Bornology.IsBounded U
  /-- `f` is holomorphic on `U`. -/
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is onto. -/
  surjOn : Set.SurjOn f U V
  /-- every fibre of `f : U → V` has at most two points (degree two). -/
  fiber_le_two : ∀ w ∈ V, {z | z ∈ U ∧ f z = w}.ncard ≤ 2
  /-- `f` has a unique critical point in `U`. -/
  unique_crit : ∃! c : ℂ, c ∈ U ∧ deriv f c = 0

namespace QuadraticLike

variable (Q : QuadraticLike)


@[simp] lemma quadraticPolyQL_f (c : ℂ) : (quadraticPolyQL c).f = fun z => z ^ 2 + c := rfl

