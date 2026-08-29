import Mathlib

/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
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

namespace Chem

/-- **Le Chatelier / van 't Hoff sign law.**

`K : ℝ → ℝ` is the equilibrium constant as a function of the absolute temperature `T > 0`.
It is positive and differentiable on `(0, ∞)` and obeys the van 't Hoff equation
`dK/dT = K · Hrxn / (R T²)`, equivalently `d (log K) / dT = Hrxn / (R T²)`,
where `R > 0` is the gas constant and `Hrxn` is the reaction enthalpy.

For an *exothermic* reaction (`Hrxn < 0`) the equilibrium constant is strictly decreasing
in the temperature on `(0, ∞)`. -/

theorem leChatelier_sign_log
    (R Hrxn : ℝ) (hR : 0 < R) (hH : Hrxn < 0)
    (K : ℝ → ℝ)
    (hKpos : ∀ T ∈ Set.Ioi (0 : ℝ), 0 < K T)
    (hKdiff : ∀ T ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ K T)
    (hvantHoff : ∀ T ∈ Set.Ioi (0 : ℝ),
      deriv (fun S => Real.log (K S)) T = Hrxn / (R * T ^ 2)) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  refine leChatelier_sign R Hrxn hR hH K hKpos hKdiff ?_
  intro T hT
  have hKT : 0 < K T := hKpos T hT
  have hlog : deriv (fun S => Real.log (K S)) T = deriv K T / K T :=
    deriv.log (hKdiff T hT) hKT.ne'
  have := hvantHoff T hT
  rw [hlog] at this
  field_simp at this ⊢
  linarith [this]

end Chem

