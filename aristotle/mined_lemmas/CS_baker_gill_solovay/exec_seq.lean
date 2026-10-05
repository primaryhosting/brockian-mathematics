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

theorem exec_seq {O : Oracle} {a b : Stmt} {na nb : (ℕ → Str) → ℕ}
    {fa fb : (ℕ → Str) → (ℕ → Str)} (ha : Exec O a na fa) (hb : Exec O b nb fb) :
    Exec O (.seq a b) (fun σ => nb (fa σ) + (na σ + 1)) (fun σ => fb (fa σ)) := by
  intro σ rest
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have h1 : (step O)^[1] (⟨Stmt.seq a b :: rest, σ⟩ : Config) = ⟨a :: b :: rest, σ⟩ := by
    simp [step]
  rw [h1, ha σ (b :: rest), hb (fa σ) rest]

