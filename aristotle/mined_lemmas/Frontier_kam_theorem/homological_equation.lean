/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- The character `x ↦ e^{2πi k x}` on the circle `ℝ / ℤ`. -/

theorem homological_equation {ω : ℝ} (hω : Irrational ω) {s : Finset ℤ} (hs : (0 : ℤ) ∉ s)
    (c : ℤ → ℂ) (x : ℝ) :
    homSol ω s c (x + ω) - homSol ω s c x = trigPoly s c x := by
  unfold homSol trigPoly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk0 : k ≠ 0 := fun h => hs (h ▸ hk)
  have hne : torusChar k ω - 1 ≠ 0 := sub_ne_zero.mpr (torusChar_ne_one hω hk0)
  rw [torusChar_add]
  field_simp

/-- **KAM theorem (persistence of invariant tori), trigonometric-polynomial case.**

Consider the integrable skew system `R (x, y) = (x + ω, y)` on the phase space
`ℝ × ℂ` (with `x` an angle variable on the circle `ℝ / ℤ` and `y` an action-type
variable), whose invariant tori are the circles `{y = a}`, each carrying the linear
flow with frequency `ω`.

Perturb it to `F (x, y) = (x + ω, y + ε * f x)`, where `f = trigPoly s c` is a
zero-mean trigonometric polynomial (`0 ∉ s`) and `ε` is the size of the perturbation.

If `ω` is irrational (a nonresonance condition making all small divisors
`e^{2πi k ω} - 1` nonzero), then the invariant tori persist: there is a periodic
"torus deformation" `U`, of size `O(‖ε‖)`, such that the change of variables
`H (x, y) = (x, y + U x)` conjugates the integrable system to the perturbed one,
`F ∘ H = H ∘ R`, and consequently each deformed torus `{y = a + U x}` is invariant
under `F`, with the induced dynamics on it the rigid rotation `x ↦ x + ω`. -/
