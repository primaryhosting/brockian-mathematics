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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma normSq_one_sub_ee (k : Fin (m + 3)) :
    Complex.normSq (1 - ee m k)
      = 2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / ((m + 3 : ℕ) : ℝ)) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / ((m + 3 : ℕ) : ℝ) with ht
  rw [ee_eq_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h := Real.sin_sq_add_cos_sq t
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  nlinarith [h]

