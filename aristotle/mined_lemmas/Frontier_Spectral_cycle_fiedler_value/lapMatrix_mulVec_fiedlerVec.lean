import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma lapMatrix_mulVec_fiedlerVec :
    (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ fiedlerVec m
      = (2 - 2 * Real.cos (cycAngle m)) • fiedlerVec m := by
  funext v
  rw [lapMatrix_cycle_mulVec]
  simp only [fiedlerVec, Pi.smul_apply, smul_eq_mul, fin_val_add_one, fin_val_sub_one,
    cos_cycAngle_mod]
  have e1 : ((v.val + (m + 2) : ℕ) : ℝ) * cycAngle m
      = ((v.val : ℝ) * cycAngle m - cycAngle m) + 2 * Real.pi := by
    push_cast
    linear_combination cycAngle_mul (m := m)
  have e2 : ((v.val + 1 : ℕ) : ℝ) * cycAngle m = (v.val : ℝ) * cycAngle m + cycAngle m := by
    push_cast; ring
  rw [e1, e2, Real.cos_add_two_pi, Real.cos_sub, Real.cos_add]
  ring

/-- The (complex) Fourier matrix of the cycle. -/
