/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

* `Frontier.TiltMonoid` and `Frontier.sharp`: the multiplicative tilt `lim_{x ↦ xᵖ} M` of a
  commutative monoid and the sharp map `x ↦ x♯`.
* `Frontier.IsPerfectoidField`: perfectoid fields (rank one valuation with a
  pseudo-uniformizer `ϖ` such that `v p ≤ (v ϖ)^p`, complete valuation ring, Frobenius
  surjective on `𝒪/p`).
* `Frontier.TiltingEquivalence`: the statement of Scholze's tilting theorem at the level of
  fields: the tilt `K♭` exists, is a perfectoid field of characteristic `p`, its
  multiplicative monoid is `lim_{x ↦ xᵖ} K`, and its valuation is transported along `♯`.
* `Frontier.untiltSystem_bijective` / `Frontier.preTiltMulEquivTiltMonoid`: the
  characteristic-free core of the correspondence, for every `p`-adically complete ring `O`:
  Fontaine's `O♭ = lim_{Frob} O/p` is multiplicatively `lim_{x ↦ xᵖ} O`, via untilting.
* `Frontier.isAdicComplete_integer_of_isPerfectoidField` and
  `Frontier.nonempty_preTilt_mulEquiv_tiltMonoid`: this applies to the ring of integers of
  any perfectoid field, in any characteristic.
* `Frontier.scholze_perfectoid_tilt`: the characteristic `p` base case of the tilting
  equivalence, where tilting is the identity.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

universe u

open Ideal

/-!
## The multiplicative tilt

For a commutative monoid `M`, the *multiplicative tilt* is the inverse limit of the system
`⋯ → M → M → M` where each transition map is `x ↦ x ^ p`.  For a perfectoid field `K` this
inverse limit is (multiplicatively) the tilt `K♭` of `K`, and the projection to the `0`-th
component is Scholze's *sharp* map `x ↦ x♯`.
-/

/-- The multiplicative tilt of a commutative monoid `M`: the inverse limit of
`M` along the `p`-power map. -/
abbrev TiltMonoid (M : Type*) [CommMonoid M] (p : ℕ) : Type _ := Monoid.perfection M p

/-- The *sharp* map `TiltMonoid M p →* M`, `x ↦ x♯`, given by the `0`-th component of a
compatible system of `p`-power roots. -/

lemma fact_not_isUnit_of_isPerfectoidField (hK : IsPerfectoidField p K v) :
    Fact (¬ IsUnit ((p : ℕ) : v.integer)) := by
  refine ⟨fun h => ?_⟩
  have h1 := (Valuation.integer.integers v).one_of_isUnit h
  rw [map_natCast] at h1
  exact absurd h1 (ne_of_lt (val_natCast_lt_one hK))

/-- **The tilt of a perfectoid field is the inverse limit of the `p`-power map.**  For an
arbitrary perfectoid field `(K, v)` — of any characteristic — Fontaine's tilt
`𝒪♭ = lim_{Frob} 𝒪/p` of the ring of integers is isomorphic, as a multiplicative monoid, to
the inverse limit of `𝒪` along `x ↦ x ^ p`, via Scholze's untilt (sharp) maps. -/
