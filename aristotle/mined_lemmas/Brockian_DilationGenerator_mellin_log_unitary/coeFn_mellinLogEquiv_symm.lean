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

theorem coeFn_mellinLogEquiv_symm (h : Lp F 2 (volume : Measure ℝ)) :
    ((mellinLogEquiv F (𝕜 := 𝕜)).symm h : ℝ → F)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] logSubSymm (h : ℝ → F) :=
  MemLp.coeFn_toLp (memLp_logSubSymm (Lp.memLp h))

/-- The scalar (complex-valued) case: the substitution `x = eᵗ` is a unitary, i.e. a `ℂ`-linear
isometry equivalence, `L²((0, ∞), ℂ) ≃ L²(ℝ, ℂ)`. -/
