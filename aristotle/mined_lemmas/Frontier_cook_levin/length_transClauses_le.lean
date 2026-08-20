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

theorem length_transClauses_le :
    (transClauses M T).length ≤ (1 + 5 * M.transList.length) * (T + 1) ^ 3 := by
  have hlen : (transClauses M T).length ≤ T + T * (M.transList.length * (2 + (T + 1) * 3)) := by
    simp only [transClauses, List.length_append]
    refine Nat.add_le_add (by simp) ?_
    refine le_trans (length_flatMap_le _ _ (M.transList.length * (2 + (T + 1) * 3)) ?_) (by simp)
    intro t _
    refine le_trans (length_flatMap_le _ _ (2 + (T + 1) * 3) ?_) (by simp)
    intro j _
    simp only [List.length_append, List.length_cons, List.length_nil]
    have hi : ((List.range (T + 1)).flatMap fun i =>
        [ implClause [TVar.mv t j, TVar.hd t i] (TVar.cell t i (M.trAt j).a),
          implClause [TVar.mv t j, TVar.hd t i] (TVar.cell (t + 1) i (M.trAt j).a'),
          implClause [TVar.mv t j, TVar.hd t i]
            (TVar.hd (t + 1) ((M.trAt j).d.move i)) ]).length ≤ (T + 1) * 3 :=
      le_trans (length_flatMap_le _ _ 3 (fun i _ => Nat.le_refl 3)) (by simp)
    omega
  have h2 : T + 1 ≤ (T + 1) ^ 3 := cube1 T
  have h3 : (T + 1) * (T + 1) ≤ (T + 1) ^ 3 := cube2 T
  have key : T * (M.transList.length * (2 + (T + 1) * 3)) ≤
      5 * M.transList.length * (T + 1) ^ 3 := by
    have e1 : T * (M.transList.length * (2 + (T + 1) * 3)) ≤
        (T + 1) * (M.transList.length * (5 * (T + 1))) := by
      have h5 : 2 + (T + 1) * 3 ≤ 5 * (T + 1) := by omega
      exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h5)
    calc T * (M.transList.length * (2 + (T + 1) * 3))
        ≤ (T + 1) * (M.transList.length * (5 * (T + 1))) := e1
      _ = 5 * M.transList.length * ((T + 1) * (T + 1)) := by ring
      _ ≤ 5 * M.transList.length * (T + 1) ^ 3 := Nat.mul_le_mul_left _ h3
  have expand : (1 + 5 * M.transList.length) * (T + 1) ^ 3 =
      (T + 1) ^ 3 + 5 * M.transList.length * (T + 1) ^ 3 := by ring
  omega

