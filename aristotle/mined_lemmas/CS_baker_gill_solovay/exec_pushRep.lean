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

theorem exec_pushRep (O : Oracle) (m r : ℕ) (b : Bool) :
    Exec O (pushRep m r b) (fun _ => 2 * m + 1)
      (fun σ => Function.update σ r (List.replicate m b ++ σ r)) := by
  induction m with
  | zero =>
      intro σ rest
      simp [pushRep, step, Function.update_eq_self]
  | succ m ih =>
      intro σ rest
      have h := exec_seq (exec_push O r b) ih σ rest
      simp only at h
      rw [show (fun _ : ℕ → Str => 2 * (m + 1) + 1) σ = (2 * m + 1) + (1 + 1) from by
        simp; ring]
      refine (h.trans ?_)
      congr 1
      funext y
      by_cases hy : y = r <;>
        simp [Function.update_apply, hy, List.replicate_succ, replicate_append_cons]


