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

theorem eval_transClauses_iff :
    CNF.eval σ (transClauses M T) = true ↔
      (∀ t < T, ∃ j, j < M.transList.length ∧ σ (TVar.mv t j) = true) ∧
      (∀ t < T, ∀ j < M.transList.length, σ (TVar.mv t j) = true →
        σ (TVar.st t (M.trAt j).q) = true ∧ σ (TVar.st (t + 1) (M.trAt j).q') = true ∧
        ∀ i ≤ T, σ (TVar.hd t i) = true →
          σ (TVar.cell t i (M.trAt j).a) = true ∧
          σ (TVar.cell (t + 1) i (M.trAt j).a') = true ∧
          σ (TVar.hd (t + 1) ((M.trAt j).d.move i)) = true) := by
  simp only [transClauses, CNF.eval_append, Bool.and_eq_true, eval_map_singleton,
    eval_flatMap, List.mem_range, Nat.lt_succ_iff, eval_atLeastOne_map,
    CNF.eval_cons, CNF.eval_nil, Bool.and_true, eval_implClause, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨hA, fun t ht j hj hmv => ?_⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hB t ht j hj
    exact ⟨h1 hmv, h2 hmv, fun i hi hhd =>
      ⟨(h3 i hi).1 ⟨hmv, hhd⟩, (h3 i hi).2.1 ⟨hmv, hhd⟩, (h3 i hi).2.2 ⟨hmv, hhd⟩⟩⟩
  · rintro ⟨hA, hB⟩
    refine ⟨hA, fun t ht j hj =>
      ⟨⟨fun hmv => (hB t ht j hj hmv).1, fun hmv => (hB t ht j hj hmv).2.1⟩,
       fun i hi => ⟨fun h => ((hB t ht j hj h.1).2.2 i hi h.2).1,
         fun h => ((hB t ht j hj h.1).2.2 i hi h.2).2.1,
         fun h => ((hB t ht j hj h.1).2.2 i hi h.2).2.2⟩⟩⟩

