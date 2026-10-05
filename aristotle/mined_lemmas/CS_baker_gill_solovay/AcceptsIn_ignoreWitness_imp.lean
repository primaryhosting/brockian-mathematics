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

theorem AcceptsIn_ignoreWitness_imp (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ)
    (h : AcceptsIn O (ignoreWitness M) x w T) : AcceptsIn O M x [] T := by
  rcases Nat.lt_or_ge T (2 * w.length + 2) with hlt | hge
  · exact absurd h.1 (ignoreWitness_not_halted O M x w hlt)
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
    have hacc : AcceptsIn O M x [] d := by
      rw [← ignoreWitness_accepts_iff O M x w d,
        show d + (2 * w.length + 2) = T from by omega]
      exact h
    exact hacc.mono (by omega)

