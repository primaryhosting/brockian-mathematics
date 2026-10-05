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

theorem stage_len_lt (n : ℕ) (s : Str) (hs : s ∈ (stage n).1) : s.length < (stage n).2 := by
  induction n with
  | zero => simp [stage] at hs
  | succ n ih =>
      rcases stage_mem_succ n s hs with h | h
      · have := ih h
        have h2 := stage_snd_le_stLen n
        have h3 := stage_snd_lt_succ n
        omega
      · have h3 := stage_snd_lt_succ n
        omega

