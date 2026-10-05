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

theorem verifier_run (O : Oracle) (x w : Str) :
    ∃ (c : ℕ) (σ' : ℕ → Str), (step O)^[c] (init verifier x w) = ⟨[], σ'⟩ ∧
      σ' 0 = [O (padTake x.length w).reverse] ∧ c ≤ 7 * x.length + 3 := by
  refine ⟨_, _, exec_init (x := x) (w := w) (exec_seq (exec_loopB O) (exec_query O 2 0)), ?_, ?_⟩
  · simp [init]
  · simp [init]
    omega

