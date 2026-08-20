/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

open MeasureTheory Set Real

namespace Brockian
namespace DilationGenerator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The substitution operator `U : (U f)(t) = e^{t/2} · f(eᵗ)`, at the level of functions. -/

theorem logSub_congr_ae {f g : ℝ → F} (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    logSub f =ᵐ[volume] logSub g := by
  filter_upwards [quasiMeasurePreserving_exp.ae_eq_comp hfg] with t ht
  simp only [logSub]
  rw [show f (Real.exp t) = (f ∘ Real.exp) t from rfl, ht]
  rfl

