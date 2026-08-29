import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

theorem Tarski_undefinability_enc :
    ¬ ArithDefinableRel (ArithTruth AForm.enc) :=
  Tarski_undefinability AForm.enc AForm.enc_injective

/-- Arithmetical definability is not a vacuous notion: equality is definable. -/
