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

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RiemannScaffold

open Complex

/-- The Riemann Hypothesis, in the form: every zero of `riemannZeta` lying in the
right half-plane `0 < Re s` lies on the critical line `Re s = 1 / 2`.

(Since `riemannZeta` has no zeros with `Re s ≥ 1`, this is the usual statement that
every nontrivial zero lies on the critical line.) -/

theorem RH_of_BrockianSystem (B : BrockianSystem) : RiemannHypothesis := by
  intro s hs hz
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · -- Reflect: `ζ (1 - s) = 0` too, and `1 - s` lies in the right half of the strip.
    exfalso
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hlt
      norm_num at hlt
    have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n h
      have hre : s.re = -(n : ℝ) := by rw [h]; simp
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hre] at hs
      linarith
    have hone : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub hsn hs1, hz, mul_zero]
    have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
    exact B.zeta_ne_zero (s := 1 - s) (by rw [hre]; linarith) (by rw [hre]; linarith) hone
  · exact heq
  · exfalso
    rcases lt_or_ge s.re 1 with h1 | h1
    · exact B.zeta_ne_zero hgt h1 hz
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz

/-- Conversely, the Riemann Hypothesis produces a Brockian system: the principal
logarithm of `ζ` works. -/
