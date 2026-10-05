/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the spin–statistics connection for a relativistic quantum field in the
Wightman framework, at the level of the two–point function, and proves it from the standard
axiomatic inputs.

## Setup

* `Frontier.Minkowski` is `ℝ^{1,3}` with quadratic form `Frontier.minkowskiSq` of signature
  `(+,-,-,-)`; two events are spacelike separated when the interval between them is negative.
* Test functions are complex valued functions on Minkowski space; two of them are *causally
  disjoint* (`Frontier.SpacelikeSupported`) when every point of the support of the first is
  spacelike separated from every point of the support of the second.
* A `Frontier.WightmanField` packages a Hilbert space with a vacuum vector, smeared field
  operators `op f`, a spin (recorded through `twoSpin`, twice the spin, so that integer spin
  means `twoSpin` even) and a choice of statistics (`fermionic`), together with three of the
  Wightman axioms that are used here:
  - hermiticity of the smeared field,
  - the (graded) local commutation relation at spacelike separation, with the sign dictated by
    the chosen statistics,
  - *weak locality*: at spacelike separation the two point function is symmetric up to the sign
    `(-1)^{2j}` dictated by the spin.  This is the Bargmann–Hall–Wightman consequence of Lorentz
    covariance, the spectral condition and the existence of Jost points.

## Results

* `Frontier.twoPoint_eq_zero_of_wrong_statistics`: if the statistics sign disagrees with the
  spin sign, the two point function vanishes for all causally disjoint test functions.
* `Frontier.op_vac_eq_zero_of_wrong_statistics`: adding the Reeh–Schlieder / edge–of–the–wedge
  input (a two point function vanishing on an open set of spacelike configurations vanishes
  identically) the field annihilates the vacuum, i.e. the theory is trivial.
* `Frontier.spin_statistics`: the spin–statistics connection.  A field that does not annihilate
  the vacuum must have statistics matching its spin: Bose statistics for integer spin, Fermi
  statistics for half–integer spin.
-/

namespace Frontier

open scoped InnerProductSpace

/-! ## Minkowski space and causal disjointness -/

/-- Minkowski spacetime `ℝ^{1,3}`, coordinates indexed by `Fin 4` with `0` the time coordinate. -/
abbrev Minkowski := Fin 4 → ℝ

/-- The Minkowski quadratic form, in signature `(+,-,-,-)`. -/

lemma pointPairField_reehSchlieder :
    (∀ f g : TestFn, SpacelikeSupported f g → pointPairField.twoPoint f g = 0) →
      ∀ f g : TestFn, pointPairField.twoPoint f g = 0 := by
  classical
  intro h f g
  exfalso
  set a : TestFn := fun x => if x = origin then 1 else 0 with ha
  set b : TestFn := fun x => if x = unitSpace then 1 else 0 with hb
  have hsupp : SpacelikeSupported a b := by
    intro x hx y hy
    have hx' : x = origin := by
      by_contra hne
      exact hx (by simp [ha, hne])
    have hy' : y = unitSpace := by
      by_contra hne
      exact hy (by simp [hb, hne])
    subst hx'; subst hy'
    exact spacelikeSep_origin_unitSpace
  have := h a b hsupp
  rw [WightmanField.twoPoint] at this
  simp [pointPairField, ha, hb, origin_ne_unitSpace, Ne.symm origin_ne_unitSpace] at this

/-- Applying the spin–statistics theorem to the nontrivial model: it is indeed bosonic. -/
example : statSign pointPairField.fermionic = spinSign pointPairField.twoSpin :=
  spin_statistics pointPairField pointPairField_reehSchlieder pointPairField_nontrivial

end Frontier

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

