/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Real

/-- The one-loop beta-function coefficient `b₀` for an `SU(N)` gauge theory with
`Nf` Dirac fermions in the fundamental representation:
`b₀ = 11 N / 3 - 2 Nf / 3`. -/
noncomputable def betaZero (N Nf : ℕ) : ℝ := 11 * (N : ℝ) / 3 - 2 * (Nf : ℝ) / 3

/-- The one-loop beta function of an `SU(N)` gauge theory with `Nf` fundamental Dirac
fermions, as a function of the gauge coupling `g`:
`β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def betaOneLoop (N Nf : ℕ) (g : ℝ) : ℝ :=
  -betaZero N Nf * g ^ 3 / (16 * π ^ 2)

/-- `b₀ > 0` exactly when `2 Nf < 11 N`. -/
theorem betaZero_pos_iff (N Nf : ℕ) : 0 < betaZero N Nf ↔ 2 * Nf < 11 * N := by
  rw [betaZero, sub_pos, div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
  constructor
  · intro h
    have : (2 * Nf : ℝ) < 11 * N := by push_cast at h ⊢; linarith
    exact_mod_cast this
  · intro h
    have : (2 * Nf : ℝ) < (11 * N : ℝ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith

/-- **Asymptotic freedom sign.** For an `SU(N)` gauge theory with `Nf` fundamental Dirac
fermions satisfying `2 Nf < 11 N` (in particular the pure-gauge case `Nf = 0` with `N ≥ 1`),
the one-loop beta function is strictly negative at every positive coupling `g`: the coupling
decreases with increasing energy scale. -/
theorem asymptotic_freedom_sign (N Nf : ℕ) (h : 2 * Nf < 11 * N) {g : ℝ} (hg : 0 < g) :
    betaOneLoop N Nf g < 0 := by
  have hb : 0 < betaZero N Nf := (betaZero_pos_iff N Nf).2 h
  have hpi : 0 < 16 * π ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  rw [betaOneLoop, div_neg_iff]
  right
  exact ⟨by nlinarith, hpi⟩

/-- The pure Yang–Mills special case: for `SU(N)` with `N ≥ 1` and no fermions,
the one-loop beta function is negative. -/
theorem asymptotic_freedom_sign_pure_gauge (N : ℕ) (hN : 1 ≤ N) {g : ℝ} (hg : 0 < g) :
    betaOneLoop N 0 g < 0 :=
  asymptotic_freedom_sign N 0 (by omega) hg

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

