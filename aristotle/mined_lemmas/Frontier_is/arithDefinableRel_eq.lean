import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

theorem arithDefinableRel_eq : ArithDefinableRel (fun a b => a = b) :=
  ⟨.eq (.var 0) (.var 1), fun _ => Iff.rfl⟩

/-- Another sanity check: the divisibility relation is arithmetically definable. -/
