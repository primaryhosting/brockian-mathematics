/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

def boseModel : WightmanField ℂ (Fin 4 → ℝ) where
  supp x := {x}
  field _ := ContinuousLinearMap.id ℂ ℂ
  fieldAdj _ := ContinuousLinearMap.id ℂ ℂ
  adj_spec _ _ _ := rfl
  vacuum := 1
  twiceSpin := 0
  stat := Statistics.bose
  locality _ _ _ := by simp [Statistics.sign]
  jost _ _ _ := by simp
  analytic h := by
    exfalso
    have := h (fun _ => 0) (fun i => if i = 1 then 1 else 0)
      (by rintro x rfl y rfl; exact spacelike_example)
    simp at this
  separating _ h := by
    exfalso
    simpa using congrArg (fun z : ℂ => z) h

