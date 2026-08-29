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

theorem const_mul_pow_le (C j n : ℕ) : C * (n + 2) ^ j ≤ (n + 2) ^ (j + C) := by
  have h1 : C ≤ (n + 2) ^ C :=
    le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by omega) C)
  calc C * (n + 2) ^ j ≤ (n + 2) ^ C * (n + 2) ^ j := Nat.mul_le_mul_right _ h1
    _ = (n + 2) ^ (j + C) := by rw [pow_add]; ring

/-- Running a whole program from the initial configuration. -/
