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

theorem exec_init {O : Oracle} {M : Stmt} {x w : Str} {n : (ℕ → Str) → ℕ}
    {f : (ℕ → Str) → (ℕ → Str)} (h : Exec O M n f) :
    (step O)^[n (init M x w).regs] (init M x w) = ⟨[], f (init M x w).regs⟩ :=
  h (init M x w).regs []

/-! ## The verifier used for the separating oracle

On input `x` and witness `w` it reads `|x|` bits off the witness and queries the
resulting string. -/

