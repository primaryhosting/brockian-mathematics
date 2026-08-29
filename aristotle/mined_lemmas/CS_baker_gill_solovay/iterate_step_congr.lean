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

theorem iterate_step_congr (O₁ O₂ : Oracle) (c : Config) (T : ℕ)
    (h : ∀ s ∈ qList O₁ c T, O₁ s = O₂ s) :
    (step O₁)^[T] c = (step O₂)^[T] c := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hT : ∀ s ∈ qList O₁ c T, O₁ s = O₂ s := by
        intro s hs
        exact h s (qList_mono O₁ c (Nat.le_succ T) s hs)
      have heq := ih hT
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← heq]
      apply step_congr
      intro s hs
      apply h
      simp only [qList, List.mem_append]
      right
      cases hq : qry ((step O₁)^[T] c) with
      | none => rw [hq] at hs; simp at hs
      | some v => rw [hq] at hs; simp at hs; simp [hs]

/-! ## The relativized classes P and NP -/

/-- `M` halts on `(x, w)` within `T` steps. -/
