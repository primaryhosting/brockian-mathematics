import Mathlib
/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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

namespace Phys

/-- Complexified Minkowski spacetime: four complex coordinates. -/
abbrev Spacetime : Type := Fin 4 → ℂ

/-- The Minkowski metric `diag (1, -1, -1, -1)`, complexified. -/

theorem cptPath_mem (t : ℝ) : cptPath t ∈ ComplexLorentzGroup := by
  have h : Complex.sin ((π : ℂ) * (t : ℂ)) ^ 2 + Complex.cos ((π : ℂ) * (t : ℂ)) ^ 2 = 1 :=
    Complex.sin_sq_add_cos_sq _
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  show cptPath t |>.transpose * minkowski * cptPath t = minkowski
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cptPath, minkowski, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.transpose_apply, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [hI]) <;>
    first
      | linear_combination h
      | linear_combination -h

