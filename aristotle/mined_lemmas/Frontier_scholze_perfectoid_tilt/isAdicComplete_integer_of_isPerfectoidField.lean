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

lemma isAdicComplete_integer_of_isPerfectoidField (hK : IsPerfectoidField p K v) :
    IsAdicComplete (Ideal.span {(p : v.integer)}) v.integer := by
  by_cases hp0 : (p : K) = 0
  · have hz : (p : v.integer) = 0 := Subtype.ext (by push_cast; exact hp0)
    rw [Ideal.span_singleton_eq_bot.mpr hz]
    infer_instance
  · have hvp0 : 0 < v (p : K) := by simpa [pos_iff_ne_zero] using hp0
    have hvp1 : v (p : K) < 1 := val_natCast_lt_one hK
    haveI : IsHausdorff (Ideal.span {(p : v.integer)}) v.integer := by
      refine ⟨fun x hx => ?_⟩
      have hval : ∀ n, v (x : K) ≤ (v (p : K)) ^ n := by
        intro n
        have := (smodEq_iff_dvd n x 0).mp (hx n)
        rw [sub_zero] at this
        exact val_le_of_dvd this
      have hx0 : v (x : K) = 0 := by
        by_contra h
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr h) hvp1
        exact absurd (hval n) (not_le.mpr hn)
      exact Subtype.ext ((Valuation.zero_iff v).mp hx0)
    haveI : IsPrecomplete (Ideal.span {(p : v.integer)}) v.integer := by
      refine ⟨fun f hf => ?_⟩
      have hval : ∀ m n, m ≤ n → v ((f m : K) - (f n : K)) ≤ (v (p : K)) ^ m := by
        intro m n hmn
        have hd := (smodEq_iff_dvd m (f m) (f n)).mp (hf hmn)
        have := val_le_of_dvd hd
        simpa using this
      have hcauchy : ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
          v ((f m : K) - (f n : K)) < ε := by
        intro ε hε
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hvp1
        refine ⟨N, fun m hm n hn => ?_⟩
        rcases le_total m n with h | h
        · exact lt_of_le_of_lt (le_trans (hval m n h)
            (NNReal.pow_antitone_exp _ _ hm (le_of_lt hvp1))) hN
        · rw [Valuation.map_sub_swap]
          exact lt_of_le_of_lt (le_trans (hval n m h)
            (NNReal.pow_antitone_exp _ _ hn (le_of_lt hvp1))) hN
      obtain ⟨L, hL1, hL2⟩ := hK.complete (fun n => (f n : K)) (fun n => (f n).2) hcauchy
      refine ⟨⟨L, hL1⟩, fun n => ?_⟩
      rw [smodEq_iff_dvd]
      refine dvd_of_val_le hp0 ?_
      have hval' : v ((f n : K) - L) ≤ (v (p : K)) ^ n := by
        obtain ⟨N, hN⟩ := hL2 ((v (p : K)) ^ n) (by positivity)
        have hk : v (L - (f (max N n) : K)) < (v (p : K)) ^ n := hN _ (le_max_left N n)
        have h1 : v ((f n : K) - (f (max N n) : K)) ≤ (v (p : K)) ^ n :=
          hval n (max N n) (le_max_right N n)
        have h2 : v ((f (max N n) : K) - L) ≤ (v (p : K)) ^ n := by
          rw [Valuation.map_sub_swap]
          exact le_of_lt hk
        have hsum : (f n : K) - L
            = ((f n : K) - (f (max N n) : K)) + ((f (max N n) : K) - L) := by ring
        rw [hsum]
        exact le_trans (v.map_add _ _) (max_le h1 h2)
      simpa using hval'
    exact IsAdicComplete.mk

/-- In a perfectoid field, `p` is not a unit in the ring of integers. -/
