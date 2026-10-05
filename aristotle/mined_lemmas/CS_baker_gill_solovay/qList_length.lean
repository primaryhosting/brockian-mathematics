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

theorem qList_length (O : Oracle) (c : Config) (T : ℕ) : (qList O c T).length ≤ T := by
  induction T with
  | zero => simp [qList]
  | succ T ih =>
      simp only [qList, List.length_append]
      have : ((qry ((step O)^[T] c)).toList).length ≤ 1 := by
        cases qry ((step O)^[T] c) <;> simp
      omega

