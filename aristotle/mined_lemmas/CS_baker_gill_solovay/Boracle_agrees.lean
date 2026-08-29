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

theorem Boracle_agrees (n : ℕ) (s : Str) (hs : s.length < (stage n).2) :
    (Boracle s = true ↔ s ∈ (stage n).1) := by
  rw [Boracle_true_iff]
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.lt_or_ge m n with h | h
    · exact stage_fst_mono (le_of_lt h) hm
    · rcases stage_mem_later h s hm with h1 | h1
      · exact h1
      · omega
  · intro h
    exact ⟨n, h⟩

/-! ## The diagonal language -/

/-- The language `{x : some string of length `|x|` is in the oracle}`. -/
