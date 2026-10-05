import RequestProject.Brockian.Weyl.DeficiencyODE

/-
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring before the import line,
so this header is rendered as an ordinary block comment with identical content.)
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

namespace Brockian.Weyl.DeficiencyODE

/-- The formally symmetric first-order Weyl differential expression
`τ u = -i u' + q u` with (continuous, real-valued in the symmetric case) potential `q`.

A function `u` is a *classical* solution of the deficiency equation `τ u = z u`
at the spectral parameter `z` when it is differentiable and satisfies the equation pointwise. -/

theorem weaklySolves_exp (z : ℂ) :
    WeaklySolvesDeficiencyODE (fun _ => 0) z (fun x : ℝ => Complex.exp (Complex.I * z * x)) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * z * x))
      (Complex.exp (Complex.I * z * x) * (Complex.I * z)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Complex.I * z * (x : ℂ)) (Complex.I * z) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (Complex.I * z)
    exact h1.cexp
  refine weaklySolvesDeficiencyODE_of_solves continuous_const
    ⟨fun x => (hd x).differentiableAt, fun x => ?_⟩
  rw [(hd x).deriv]
  simp only [zero_mul]
  linear_combination (-z * Complex.exp (Complex.I * z * x)) * Complex.I_sq

end Brockian.Weyl.DeficiencyODE

