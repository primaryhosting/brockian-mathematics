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

theorem dupStr_append (l₁ l₂ : Str) : dupStr (l₁ ++ l₂) = dupStr l₁ ++ dupStr l₂ := by
  induction l₁ with
  | nil => simp [dupStr]
  | cons b t ih => simp [dupStr, ih]

/-- Move the content of register `0` onto register `2`, doubling each bit. -/
