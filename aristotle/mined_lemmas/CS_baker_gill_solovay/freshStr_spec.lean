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

theorem freshStr_spec (l : ℕ) (Q : List Str) (h : Q.length < 2 ^ l) :
    (freshStr l Q).length = l ∧ freshStr l Q ∉ Q := by
  have hex := exists_fresh l Q h
  simp only [freshStr, dif_pos hex]
  exact hex.choose_spec

/-! ## The stage construction of the separating oracle -/

open Classical in
/-- Stage `n` of the construction: the strings put into the oracle so far,
together with a bound below which the oracle is already decided. -/
