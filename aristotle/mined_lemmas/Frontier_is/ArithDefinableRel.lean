import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

def ArithDefinableRel (R : Nat → Nat → Prop) : Prop :=
  ∃ φ : AForm, ∀ v : Nat → Nat, (φ.Sat v ↔ R (v 0) (v 1))

/-- *Arithmetical truth* relative to a Gödel numbering `code` of arithmetical formulas:
`ArithTruth code m n` holds iff `m` is the Gödel number of an arithmetical formula that is
true in the standard model when its variables are given the value `n`.  This is the
satisfaction relation of `(Nat, 0, 1, +, *, =)`, transported along the numbering. -/
