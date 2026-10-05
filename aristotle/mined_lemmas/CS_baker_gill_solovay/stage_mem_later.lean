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

theorem stage_mem_later {n m : ℕ} (h : n ≤ m) (s : Str) (hs : s ∈ (stage m).1) :
    s ∈ (stage n).1 ∨ (stage n).2 ≤ s.length := by
  induction m with
  | zero =>
      have : n = 0 := by omega
      subst this
      exact Or.inl hs
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · rcases stage_mem_succ m s hs with h1 | h1
        · exact ih (by omega) h1
        · right
          have : (stage n).2 ≤ (stage m).2 := stage_snd_mono (by omega)
          have h2 := stage_snd_le_stLen m
          omega
      · have : n = m + 1 := by omega
        subst this
        exact Or.inl hs

/-- The separating oracle. -/
