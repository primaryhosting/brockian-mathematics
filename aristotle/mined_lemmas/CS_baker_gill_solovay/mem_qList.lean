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

theorem mem_qList (O : Oracle) (c : Config) (T : ℕ) (s : Str) (h : s ∈ qList O c T) :
    ∃ j, j < T ∧ qry ((step O)^[j] c) = some s := by
  induction T with
  | zero => simp [qList] at h
  | succ T ih =>
      simp only [qList, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨j, hj, hq⟩ := ih h
        exact ⟨j, by omega, hq⟩
      · refine ⟨T, by omega, ?_⟩
        cases hq : qry ((step O)^[T] c) with
        | none => rw [hq] at h; simp at h
        | some v =>
            rw [hq] at h
            simp at h
            subst h
            simp_all

