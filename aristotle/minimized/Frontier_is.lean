import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

theorem is satisfiable and the theorem is not vacuous.  We also record that the notion of
arithmetical definability used there is non-trivial (some relations *are* definable).
-/

namespace Frontier

/-- A Gödel numbering of arithmetical terms, using Cantor pairing. -/
