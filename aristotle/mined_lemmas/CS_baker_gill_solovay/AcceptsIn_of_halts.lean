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

theorem AcceptsIn_of_halts {O : Oracle} {M : Stmt} {x w : Str} {T T' : ℕ}
    (hH : Halts O M x w T) (hle : T ≤ T') (h : AcceptsIn O M x w T') :
    AcceptsIn O M x w T := by
  have heq : runFor O M x w T' = runFor O M x w T := iterate_step_stable O _ hH hle
  unfold AcceptsIn at h ⊢
  rw [heq] at h
  exact h

/-- `L ∈ P^O`: some machine decides `L` (with empty witness), halting within
time `(n+2)^k`. -/
