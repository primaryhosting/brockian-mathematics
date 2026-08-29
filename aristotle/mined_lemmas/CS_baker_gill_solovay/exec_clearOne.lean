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

theorem exec_clearOne (O : Oracle) :
    Exec O clearOne (fun σ => 2 * (σ 1).length + 1)
      (fun σ r => if r = 1 then [] else σ r) := by
  have key : ∀ (w : Str) (σ : ℕ → Str), σ 1 = w → ∀ rest : List Stmt,
      (step O)^[2 * w.length + 1] (⟨clearOne :: rest, σ⟩ : Config)
        = ⟨rest, fun r => if r = 1 then [] else σ r⟩ := by
    intro w
    induction w with
    | nil =>
        intro σ h1 rest
        have h : (step O)^[1] (⟨clearOne :: rest, σ⟩ : Config) = ⟨rest, σ⟩ := by
          simp [clearOne, step, h1]
        simpa using h.trans (by
          congr 1
          funext y
          by_cases hy : y = 1 <;> simp [hy, h1])
    | cons b t ih =>
        intro σ h1 rest
        set σ' : ℕ → Str := fun r => if r = 1 then t else σ r with hσ'
        have h2 : (step O)^[2] (⟨clearOne :: rest, σ⟩ : Config) = ⟨clearOne :: rest, σ'⟩ := by
          have hs : (step O)^[1] (⟨clearOne :: rest, σ⟩ : Config)
              = ⟨Stmt.pop 1 :: clearOne :: rest, σ⟩ := by
            simp [clearOne, step, h1]
          rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, hs,
            exec_pop O 1 σ (clearOne :: rest)]
          congr 1
          funext y
          by_cases hy : y = 1 <;> simp [hσ', Function.update_apply, hy, h1]
        rw [show 2 * (b :: t).length + 1 = (2 * t.length + 1) + 2 from by
          simp [List.length_cons]; ring, Function.iterate_add_apply, h2,
          ih σ' (by simp [hσ']) rest]
        congr 1
        funext y
        by_cases hy : y = 1 <;> simp [hσ', hy]
  intro σ rest
  exact key (σ 1) σ rfl rest

end CS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


import Mathlib

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## Strings, oracles, languages -/

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a decision procedure for strings (a language, given by its
characteristic function). -/
abbrev Oracle := Str → Bool

/-! ## An oracle machine model

A machine is a structured program operating on countably many stack registers
holding binary strings.  Each elementary instruction costs one step, and each
instruction changes the content of a register by at most one bit, so that in
`t` steps a register can grow by at most `t` bits.  Register `0` holds the
input (and, at the end of a computation, the answer bit on top), register `1`
holds the witness (nondeterministic guess) and all other registers start empty.
-/

/-- Programs. `query s r` queries the oracle on the content of register `s` and
pushes the answer bit onto register `r`.  `padAux m r` pushes `m` bits onto
register `r`, one per step (so it costs `m + 1` steps); `pad k s r` starts such
a block-write of `(|reg s| + 2) ^ k` bits. -/
inductive Stmt where
  | skip : Stmt
  | push : ℕ → Bool → Stmt
  | pop : ℕ → Stmt
  | query : ℕ → ℕ → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : ℕ → Stmt → Stmt → Stmt
  | wh : ℕ → Stmt → Stmt
  | padAux : ℕ → ℕ → Stmt
  | pad : ℕ → ℕ → ℕ → Stmt
  deriving DecidableEq

/-- A configuration: the list of statements still to be executed, and the
contents of the registers. -/
structure Config where
  ctrl : List Stmt
  regs : ℕ → Str

/-- One step of computation. -/
