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

theorem stage_mem_succ (n : ℕ) (s : Str) (hs : s ∈ (stage (n + 1)).1) :
    s ∈ (stage n).1 ∨ s.length = stLen n := by
  rw [stage_fst_succ] at hs
  split at hs
  · exact Or.inl hs
  · rcases Finset.mem_insert.1 hs with h | h
    · right
      subst h
      by_cases hQ : (qList (oracleOf (stage n).1) (init (enumPair n).1 (stInput n) [])
          (stTime n)).length < 2 ^ (stLen n)
      · exact (freshStr_spec _ _ hQ).1
      · exfalso
        apply hQ
        have h1 := qList_length (oracleOf (stage n).1)
          (init (enumPair n).1 (stInput n) []) (stTime n)
        have h2 : stTime n < 2 ^ (stLen n) := chooseLen_big (stage n).2 (enumPair n).2
        omega
    · exact Or.inl h

