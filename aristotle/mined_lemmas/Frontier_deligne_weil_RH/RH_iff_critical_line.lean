/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

/-- The cohomological data attached to a smooth projective variety of dimension `dim`
over the finite field `𝔽_q`: for each degree `i`, the multiset `eigen i` of eigenvalues
of the geometric Frobenius acting on the `i`-th ℓ-adic cohomology group. -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The base field is a genuine finite field. -/
  hq : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- Multiset of Frobenius eigenvalues in cohomological degree `i`. -/
  eigen : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanish : ∀ i, 2 * dim < i → eigen i = 0
  /-- Frobenius acts invertibly, so all eigenvalues are nonzero. -/
  nonzero : ∀ i, ∀ a ∈ eigen i, a ≠ 0

namespace WeilData

variable (W : WeilData)

/-- The Lefschetz trace formula prediction for the number of `𝔽_{q^m}`-rational points:
`N_m = ∑_i (-1)^i tr(Frob^m ∣ H^i)`. -/

theorem RH_iff_critical_line (W : WeilData) :
    W.RH ↔ ∀ i, ∀ a ∈ W.eigen i, ∀ s : ℂ, a * (W.q : ℂ) ^ (-s) = 1 → s.re = (i : ℝ) / 2 := by
  have hq0 : (0 : ℝ) < (W.q : ℝ) := by
    have := W.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  have hq1 : (W.q : ℝ) ≠ 1 := by
    have h : W.q ≠ 1 := by have := W.hq; omega
    exact_mod_cast h
  have hqC : (W.q : ℂ) ≠ 0 := by
    have h : W.q ≠ 0 := by have := W.hq; omega
    simpa using h
  have hlogq : Real.log W.q ≠ 0 := by
    have h1 : (1 : ℝ) < (W.q : ℝ) := by exact_mod_cast W.hq
    exact ne_of_gt (Real.log_pos h1)
  constructor
  · intro hRH i a ha s hs
    have hnorm := hRH i a ha
    have h1 : ‖a‖ * ‖(W.q : ℂ) ^ (-s)‖ = 1 := by rw [← norm_mul, hs, norm_one]
    have h2 : ‖(W.q : ℂ) ^ (-s)‖ = (W.q : ℝ) ^ (-s).re := by
      rw [← Complex.ofReal_natCast]
      exact Complex.norm_cpow_eq_rpow_re_of_pos hq0 _
    rw [hnorm, h2, ← Real.rpow_add hq0] at h1
    have h4 : (W.q : ℝ) ^ ((i : ℝ) / 2 + (-s).re) = (W.q : ℝ) ^ (0 : ℝ) := by
      rw [h1, Real.rpow_zero]
    have h3 := (Real.rpow_right_inj hq0 hq1).mp h4
    simp only [Complex.neg_re] at h3
    linarith
  · intro H i a ha
    have hane' : a ≠ 0 := W.nonzero i a ha
    have hL : Complex.log (W.q : ℂ) = ((Real.log W.q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (le_of_lt hq0)]
    set s : ℂ := Complex.log a / ((Real.log W.q : ℝ) : ℂ) with hsdef
    have hLne : ((Real.log W.q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlogq
    have key : a * (W.q : ℂ) ^ (-s) = 1 := by
      rw [Complex.cpow_def_of_ne_zero hqC, hL, hsdef]
      field_simp
      rw [Complex.exp_neg, Complex.exp_log hane']
      field_simp
    have hre := H i a ha s key
    have hsre : s.re = Real.log ‖a‖ / Real.log W.q := by
      rw [hsdef, Complex.div_ofReal_re, Complex.log_re]
    rw [hsre] at hre
    have hlog : Real.log ‖a‖ = Real.log W.q * ((i : ℝ) / 2) := by
      field_simp at hre
      linarith [hre]
    have hane : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr hane'
    rw [Real.rpow_def_of_pos hq0, ← hlog, Real.exp_log hane]

/-! ### Poincaré duality: reduction of the Riemann hypothesis to degrees `≤ dim` -/

/-- Poincaré duality for the Frobenius eigenvalues: in complementary degrees `i` and
`2·dim - i` the eigenvalues correspond under `a ↦ q^dim / a`. -/
