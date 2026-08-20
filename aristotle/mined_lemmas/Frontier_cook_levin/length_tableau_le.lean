/-
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4.28 does not allow a module docstring before the import block, so this header
is a plain block comment; the text is otherwise verbatim.)
-/

import Mathlib
import RequestProject.CookLevin.Sat
import RequestProject.CookLevin.Machine
import RequestProject.CookLevin.Tableau
import RequestProject.CookLevin.Forward
import RequestProject.CookLevin.Backward
import RequestProject.CookLevin.Size
import RequestProject.CookLevin.Sanity
import RequestProject.CookLevin.Certificate

/-!
## The Cook–Levin theorem

`Frontier.cook_levin` states that SAT is `NP`-hard: every language `L` in `NP` is reduced to
`SATLang`, the set of satisfiable CNF formulas over `ℕ`, by the explicit computable map
`Frontier.reduction`, whose output is of polynomial size.

The complexity class `NP` is modelled by single-tape nondeterministic Turing machines
(`Frontier.NTM`) with a polynomial time bound (`Frontier.InNP`), and the reduction is the
classical *tableau* construction: `Frontier.tableau M x T` is a CNF formula whose satisfying
assignments are exactly the accepting computations of `M` on `x` of length `T`
(`Frontier.tableau_satisfiable_iff`).

### Sources and scope

* Mathlib (at the version pinned by this project) contains no complexity theory: there is no
  definition of `P`, `NP`, of polynomial-time reductions, or of SAT, and no Cook–Levin
  statement.  Everything below is therefore developed from scratch, except for the CNF
  datatype `Std.Sat.CNF` and its relabelling API, which come from the Lean core library.
* What is proved is the hard half of the Cook–Levin theorem, `NP`-hardness of SAT, for
  many-one reductions that are computable Lean functions of polynomially bounded output
  size.  Two ingredients of the textbook statement are *not* formalised here: that the
  reduction runs in polynomial *time* (this project fixes no cost model for computing the
  reduction itself), and the easy half `SAT ∈ NP` (which would require programming and
  verifying a nondeterministic Turing machine that parses and evaluates encoded formulas).
  `Frontier.satisfiable_iff_exists_certificate` records the certificate characterisation of
  satisfiability that underlies the easy half.
-/

namespace Frontier

open Std.Sat

/-! ### Encoding the tableau variables by natural numbers -/

/-- Numerical code of a tape symbol. -/

theorem length_tableau_le :
    (tableau M x T).length ≤
      (M.numStates ^ 2 + 5 * M.transList.length + 22) * (T + 1) ^ 3 := by
  have e : (tableau M x T).length =
      (stateClauses M T).length + (headClauses T).length + (cellClauses T).length +
      (initClauses M x T).length + (acceptClauses M T).length +
      (headBoundClauses T).length + (transClauses M T).length +
      (inertiaClauses T).length := by
    simp only [tableau, List.length_append]
  have h1 := length_stateClauses_le M T
  have h2 := length_headClauses_le T
  have h3 := length_cellClauses_le T
  have h4 := length_initClauses_le M x T
  have h5 := length_acceptClauses_le M T
  have h6 := length_headBoundClauses_le T
  have h7 := length_transClauses_le M T
  have h8 := length_inertiaClauses_le T
  have expand : (M.numStates ^ 2 + 5 * M.transList.length + 22) * (T + 1) ^ 3 =
      (1 + M.numStates ^ 2) * (T + 1) ^ 3 + 2 * (T + 1) ^ 3 + 10 * (T + 1) ^ 3 +
      3 * (T + 1) ^ 3 + (T + 1) ^ 3 + (T + 1) ^ 3 +
      (1 + 5 * M.transList.length) * (T + 1) ^ 3 + 3 * (T + 1) ^ 3 := by ring
  omega

end Frontier

/-
From a satisfying assignment of the tableau back to an accepting computation.
-/
import Mathlib
import RequestProject.CookLevin.Tableau

namespace Frontier

open Std.Sat

variable {M : NTM} {x : List Bool} {T : ℕ} {σ : TVar → Bool}

open Classical in
/-- The state described by the assignment `σ` at time `t`. -/
