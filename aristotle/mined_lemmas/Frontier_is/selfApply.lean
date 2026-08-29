import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

private def selfApply (T : AForm) : AForm :=
  .ex 1 (.and (.eq (.var 0) (.var 1)) T)

