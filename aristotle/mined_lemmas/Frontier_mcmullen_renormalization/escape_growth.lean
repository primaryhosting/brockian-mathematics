/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

lemma escape_growth (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) {z : ℂ} (hz : R < ‖z‖) (n : ℕ) :
    ‖z‖ + n * (R ^ 2 - R - ‖c‖) ≤ ‖(qmap c)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      set d : ℝ := R ^ 2 - R - ‖c‖ with hd
      have hd0 : 0 < d := by simp only [hd]; linarith
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have ht : R < ‖(qmap c)^[n] z‖ := by nlinarith
      have hstep : ‖(qmap c)^[n] z‖ ^ 2 - ‖c‖ ≤ ‖(qmap c)^[n + 1] z‖ := by
        rw [Function.iterate_succ_apply']
        exact norm_qmap_ge c _
      have hsq : ‖(qmap c)^[n] z‖ + d ≤ ‖(qmap c)^[n] z‖ ^ 2 - ‖c‖ := by
        simp only [hd]; nlinarith
      have hfin : ‖z‖ + (n : ℝ) * d + d ≤ ‖(qmap c)^[n + 1] z‖ := by linarith
      push_cast
      calc ‖z‖ + ((n : ℝ) + 1) * d = ‖z‖ + (n : ℝ) * d + d := by ring
        _ ≤ ‖(qmap c)^[n + 1] z‖ := hfin

/-- Orbits leaving the disk of radius `R` are unbounded. -/
