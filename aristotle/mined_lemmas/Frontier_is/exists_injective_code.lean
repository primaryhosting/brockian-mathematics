import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

theorem exists_injective_code : ∃ code : AForm → Nat, Function.Injective code :=
  ⟨AForm.enc, AForm.enc_injective⟩

/-- Tarski's undefinability theorem for the concrete Gödel numbering `AForm.enc`. -/
