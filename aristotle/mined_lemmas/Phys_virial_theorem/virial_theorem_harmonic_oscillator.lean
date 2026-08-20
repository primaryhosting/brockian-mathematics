/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology

namespace Phys

/-- The auxiliary "virial current"
`F x = x * ψ' x ^ 2 - x * (V x - E) * ψ x ^ 2 + ψ x * ψ' x`,
whose derivative is exactly `2 * ψ' x ^ 2 - x * V' x * ψ x ^ 2` for a solution of the
stationary Schrödinger equation. -/

theorem virial_theorem_harmonic_oscillator :
    2 * (∫ x : ℝ, (-x * Real.exp (-x ^ 2 / 2)) ^ 2)
      = ∫ x : ℝ, x * (2 * x) * (Real.exp (-x ^ 2 / 2)) ^ 2 := by
  have hzero : virialCurrent (fun x : ℝ => Real.exp (-x ^ 2 / 2))
      (fun x : ℝ => -x * Real.exp (-x ^ 2 / 2)) (fun x : ℝ => x ^ 2) 1 = fun _ => (0 : ℝ) := by
    funext x
    simp only [virialCurrent]
    ring
  have hinner : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h using 1
    ring
  refine virial_theorem (fun x => Real.exp (-x ^ 2 / 2)) (fun x => -x * Real.exp (-x ^ 2 / 2))
    (fun x => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)) (fun x => x ^ 2) (fun x => 2 * x) 1
    (fun x => by simpa [mul_comm] using (hinner x).exp) (fun x => ?_)
    (fun x => by simpa using hasDerivAt_pow 2 x) (fun x => by ring) ?_ ?_ ?_ ?_
  · have h : HasDerivAt (fun y : ℝ => -y * Real.exp (-y ^ 2 / 2))
        (-1 * Real.exp (-x ^ 2 / 2) + -x * (Real.exp (-x ^ 2 / 2) * -x)) x :=
      ((hasDerivAt_id x).neg).mul (hinner x).exp
    convert h using 1
    ring
  · refine integrable_sq_mul_gaussian.congr (Filter.Eventually.of_forall fun x => ?_)
    show x ^ 2 * Real.exp (-1 * x ^ 2) = (-x * Real.exp (-x ^ 2 / 2)) ^ 2
    rw [mul_pow, neg_sq, exp_sq_aux]
  · refine (integrable_sq_mul_gaussian.const_mul 2).congr (Filter.Eventually.of_forall fun x => ?_)
    show 2 * (x ^ 2 * Real.exp (-1 * x ^ 2)) = x * (2 * x) * (Real.exp (-x ^ 2 / 2)) ^ 2
    rw [exp_sq_aux]; ring
  · rw [hzero]; exact tendsto_const_nhds
  · rw [hzero]; exact tendsto_const_nhds

end Phys

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

