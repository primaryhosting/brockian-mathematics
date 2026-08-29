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

theorem iterate_step_stable (O : Oracle) (c : Config) {n : ℕ}
    (h : ((step O)^[n] c).ctrl = []) {m : ℕ} (hm : n ≤ m) :
    (step O)^[m] c = (step O)^[n] c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show n + d = d + n from by omega, Function.iterate_add_apply,
    iterate_step_halted O h]

