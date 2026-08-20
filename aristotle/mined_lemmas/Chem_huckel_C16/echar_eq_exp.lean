/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import commands, so the required
header appears here as an ordinary block comment; the text is otherwise verbatim.)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₆`, i.e. the Hückel matrix of
cyclic C₁₆ in units where the Coulomb integral is `0` and the resonance integral is `1`. -/

theorem echar_eq_exp (j : Fin 16) :
    echar j = Complex.exp (((2 * Real.pi * (j : ℕ) / 16 : ℝ) : ℂ) * Complex.I) := by
  rw [echar, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

