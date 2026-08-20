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

lemma isPerfectoidField_of_perfectRing [PerfectRing K p]
    (hu : ∃ w : K, 0 < v w ∧ v w < 1 ∧ v (p : K) ≤ (v w) ^ p)
    (hc : ∀ a : ℕ → K, (∀ n, v (a n) ≤ 1) →
      (∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, v (a m - a n) < ε) →
      ∃ L : K, v L ≤ 1 ∧ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n ≥ N, v (L - a n) < ε) :
    IsPerfectoidField p K v where
  pseudoUniformizer := hu
  complete := hc
  frobSurj x hx := by
    refine ⟨(frobeniusEquiv K p).symm x, ?_, ?_⟩
    · by_contra h
      push_neg at h
      have hpow : (1 : ℝ≥0) < (v ((frobeniusEquiv K p).symm x)) ^ p :=
        one_lt_pow₀ h (Nat.Prime.ne_zero Fact.out)
      rw [← map_pow, frobeniusEquiv_symm_pow_p] at hpow
      exact absurd hx (not_le.mpr hpow)
    · rw [frobeniusEquiv_symm_pow_p, sub_self, map_zero]
      exact zero_le _

/-- In characteristic `p` the element `p` of the ring of integers is `0`, hence not a unit. -/
instance fact_not_isUnit_natCast_integer : Fact (¬ IsUnit ((p : ℕ) : v.integer)) := by
  refine ⟨?_⟩
  rw [CharP.cast_eq_zero]
  simp

/-- In characteristic `p` the `p`-adic topology on the ring of integers is discrete, so the
ring of integers is trivially `p`-adically complete. -/
instance isAdicComplete_integer : IsAdicComplete (Ideal.span {((p : ℕ) : v.integer)})
    v.integer := by
  have hspan : Ideal.span {((p : ℕ) : v.integer)} = ⊥ := by
    rw [CharP.cast_eq_zero]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  rw [hspan]
  infer_instance

/-- The ring of integers of a perfectoid field of characteristic `p` is perfect. -/
