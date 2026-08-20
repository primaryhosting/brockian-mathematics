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

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex

namespace Brockian.RiemannScaffold

/-!
## Overview

A *Brockian system* is the datum of a one-sided spectral bound for the Riemann zeta function
inside the critical strip: every zero of `ζ` with `0 < re s < 1` satisfies `1/2 ≤ re s`.

The target theorem `RH_of_BrockianSystem` says that this one-sided bound already implies the
full Riemann Hypothesis in the form stated in Mathlib (`RiemannHypothesis`), with **no further
hypotheses**: the previously assumed reflection principle for zeros and the treatment of the
regions `re s ≤ 0` and `1 ≤ re s` are discharged here from Mathlib, via

* `riemannZeta_one_sub` (the functional equation),
* `riemannZeta_ne_zero_of_one_le_re` (non-vanishing on `1 ≤ re s`),
* `riemannZeta_zero` (the value `ζ 0 = -1/2`),
* `Complex.cos_eq_zero_iff` and `Complex.Gamma_ne_zero`.
-/

/-- **Brockian system**: a one-sided bound `1/2 ≤ re s` for the zeros of `ζ` in the open
critical strip. -/
structure BrockianSystem : Prop where
  /-- Every zero of `ζ` in the open critical strip lies in the half plane `1/2 ≤ re s`. -/
  halfPlane_bound : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 1 / 2 ≤ s.re

/-- **Reflection principle** (formerly the named hypothesis, now discharged): zeros of `ζ` in
the open critical strip are symmetric under `s ↦ 1 - s`. Immediate from the functional equation
`riemannZeta_one_sub`. -/

theorem zeta_zero_one_sub {s : ℂ} (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 := by
  have hne : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    rw [hn] at h0
    simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at h0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  rw [riemannZeta_one_sub hne hne1, hs, mul_zero]

/-- A zero of `ζ` with `re s ≤ 0` must be one of the trivial zeros `-2(n+1)`.

Proof: put `w = 1 - s`, so `1 ≤ re w`. The functional equation `riemannZeta_one_sub` expresses
`ζ s = ζ (1 - w)` as a product in which every factor except `cos (π w / 2)` is nonzero
(`riemannZeta_ne_zero_of_one_le_re`, `Complex.Gamma_ne_zero`, `Complex.cpow_ne_zero_iff`), so
`cos (π w / 2) = 0`, i.e. `w = 2k + 1` with `k ≥ 0` by `Complex.cos_eq_zero_iff`. Then
`s = -2k`, and `k = 0` is impossible because `ζ 0 = -1/2 ≠ 0` (`riemannZeta_zero`). -/
