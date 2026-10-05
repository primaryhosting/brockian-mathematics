/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Model

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## A calculus for reasoning about program execution -/

/-- `Exec O S n f` says: started with registers `σ`, the statement `S` terminates
after exactly `n σ` steps, leaving the registers in state `f σ` (and the rest of
the control stack untouched). -/

theorem AcceptsIn_congr {O₁ O₂ : Oracle} {M : Stmt} {x w : Str} {T : ℕ}
    (h : ∀ s ∈ qList O₁ (init M x w) T, O₁ s = O₂ s) :
    (AcceptsIn O₁ M x w T ↔ AcceptsIn O₂ M x w T) := by
  unfold AcceptsIn runFor
  rw [iterate_step_congr O₁ O₂ (init M x w) T h]

/-! ## Choosing a string that was not queried -/

