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

theorem exec_ite {O : Oracle} {r : ℕ} {a b : Stmt} {na nb : (ℕ → Str) → ℕ}
    {fa fb : (ℕ → Str) → (ℕ → Str)} (ha : Exec O a na fa) (hb : Exec O b nb fb) :
    Exec O (.ite r a b)
      (fun σ => (if (σ r).head? = some true then na σ else nb σ) + 1)
      (fun σ => if (σ r).head? = some true then fa σ else fb σ) := by
  intro σ rest
  rw [Function.iterate_add_apply]
  have h1 : (step O)^[1] (⟨Stmt.ite r a b :: rest, σ⟩ : Config)
      = ⟨(if (σ r).head? = some true then a else b) :: rest, σ⟩ := by
    simp [step]
  rw [h1]
  by_cases h : (σ r).head? = some true
  · simp only [h, if_pos]
    exact ha σ rest
  · simp only [h, if_neg, if_false]
    exact hb σ rest

