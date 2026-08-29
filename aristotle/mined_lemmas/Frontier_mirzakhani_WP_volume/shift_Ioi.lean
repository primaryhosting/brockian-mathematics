/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

set_option grind.warning false

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

lemma shift_Ioi (f : ℝ → ℝ) (c : ℝ) :
    ∫ x in Ioi (0:ℝ), f (x + c) = ∫ y in Ioi c, f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have hind : ∀ x : ℝ, (Ioi (0:ℝ)).indicator (fun x => f (x + c)) x
      = (Ioi c).indicator f (x + c) := by
    intro x
    simp [Set.indicator_apply]
  simp_rw [hind]
  exact integral_add_right_eq_self (fun y => (Ioi c).indicator f y) c

/-! ## The Fermi-type integral `∫₀^∞ y / (1 + e^{y/2}) dy = π²/3` -/

