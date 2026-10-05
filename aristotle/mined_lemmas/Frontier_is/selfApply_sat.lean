import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

private theorem selfApply_sat (T : AForm) (v : Nat → Nat) :
    (selfApply T).Sat v ↔ T.Sat (upd v 1 (v 0)) := by
  constructor
  · intro hex
    have hex' : ∃ m : Nat, (AForm.and (.eq (.var 0) (.var 1)) T).Sat (upd v 1 m) := hex
    match hex' with
    | ⟨m, hm, hT⟩ =>
      have hvm : v 0 = m := by
        have h0 : ATerm.eval (upd v 1 m) (.var 0) = ATerm.eval (upd v 1 m) (.var 1) := hm
        simpa [ATerm.eval, upd] using h0
      exact hvm ▸ hT
  · intro hT
    refine ⟨v 0, ?_, hT⟩
    show ATerm.eval (upd v 1 (v 0)) (.var 0) = ATerm.eval (upd v 1 (v 0)) (.var 1)
    simp [ATerm.eval, upd]

/-- **Tarski's undefinability theorem, diagonal form.**  For any injective Gödel numbering
`code`, the *diagonal* of arithmetical truth, i.e. the set of Gödel numbers `n` of
arithmetical formulas that are true of `n` itself, is not arithmetically definable. -/
