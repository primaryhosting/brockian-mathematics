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

noncomputable def logSubSymm (h : ℝ → F) : ℝ → F :=
  fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x)

/-- **Change of variables `x = eᵗ`.** For any function `g : ℝ → F` (no integrability or
measurability assumption is needed: both sides are `0` when the integrand is not integrable),
the integral of `g` over `(0, ∞)` equals the integral of `eᵗ • g (eᵗ)` over `ℝ`. -/
