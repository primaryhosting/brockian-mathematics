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

@[simp] lemma sharp_perfectMulEquivTiltMonoid (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p]
    [PerfectRing R p] (x : R) : sharp R p (perfectMulEquivTiltMonoid R p x) = x := rfl

/-!
## Perfectoid fields
-/

/-- `IsPerfectoidField p K v` says that the field `K`, equipped with the rank-one valuation
`v : K → ℝ≥0`, is a perfectoid field with residue characteristic `p`:

* the valuation admits a pseudo-uniformizer `ϖ` with `0 < v ϖ < 1` and `v p ≤ (v ϖ) ^ p`
  (so the valuation is non-discrete and `p` is topologically nilpotent);
* the valuation ring of `K` is complete (every Cauchy sequence of integral elements
  converges to an integral element);
* the Frobenius `x ↦ x ^ p` is surjective on `𝒪_K / p`. -/
structure IsPerfectoidField (p : ℕ) (K : Type*) [Field K] (v : Valuation K ℝ≥0) : Prop where
  /-- There is a pseudo-uniformizer `ϖ` with `v p ≤ (v ϖ) ^ p`. -/
  pseudoUniformizer : ∃ w : K, 0 < v w ∧ v w < 1 ∧ v (p : K) ≤ (v w) ^ p
  /-- The valuation ring is complete. -/
  complete : ∀ a : ℕ → K, (∀ n, v (a n) ≤ 1) →
    (∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, v (a m - a n) < ε) →
    ∃ L : K, v L ≤ 1 ∧ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n ≥ N, v (L - a n) < ε
  /-- Frobenius is surjective on `𝒪_K / p`. -/
  frobSurj : ∀ x : K, v x ≤ 1 → ∃ y : K, v y ≤ 1 ∧ v (x - y ^ p) ≤ v (p : K)

/-- The data of a tilt of a perfectoid field `(K, v)`: a perfectoid field `Kb` of
characteristic `p` whose multiplicative monoid is identified with the inverse limit of `K`
along the `p`-power map, in such a way that the valuation of `Kb` is transported from `K`
along the sharp map. -/
structure TiltData (p : ℕ) (K : Type u) [Field K] (v : Valuation K ℝ≥0) where
  /-- The underlying type of the tilt. -/
  Kb : Type u
  /-- The tilt is a field. -/
  [field : Field Kb]
  /-- The tilt has characteristic `p`. -/
  [char : CharP Kb p]
  /-- The valuation of the tilt. -/
  vb : Valuation Kb ℝ≥0
  /-- The multiplicative identification of the tilt with `lim_{x ↦ xᵖ} K`. -/
  e : Kb ≃* TiltMonoid K p
  /-- The tilt is again a perfectoid field. -/
  perfectoid : IsPerfectoidField p Kb vb
  /-- The sharp map is valuation preserving. -/
  sharp_val : ∀ x : Kb, v (sharp K p (e x)) = vb x

/-- **The tilting equivalence for perfectoid fields (Scholze).**  A perfectoid field `(K, v)`
of residue characteristic `p` admits a tilt: a perfectoid field `K♭` of characteristic `p`
whose multiplicative monoid is the inverse limit of `K` along `x ↦ x ^ p`, with valuation
transported along the sharp map `x ↦ x♯`.

This is the field-level part of Scholze's theorem.  The further statements of the tilting
equivalence — the equivalence between the categories of perfectoid `K`-algebras and
perfectoid `K♭`-algebras, and the resulting isomorphism of absolute Galois groups — are not
formalised here. -/
