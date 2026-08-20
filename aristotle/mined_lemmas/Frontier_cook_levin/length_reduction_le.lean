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

theorem length_reduction_le (M : NTM) (c k : ℕ) (x : List Bool) :
    (reduction M c k x).length ≤
      (M.numStates ^ 2 + 5 * M.transList.length + 22) * (c + 1) ^ 3 *
        (x.length + 1) ^ (3 * k) := by
  have h1 : (reduction M c k x).length = (tableau M x (c * (x.length + 1) ^ k)).length := by
    simp [reduction, CNF.relabel]
  have h2 := length_tableau_le M x (c * (x.length + 1) ^ k)
  have h3 : c * (x.length + 1) ^ k + 1 ≤ (c + 1) * (x.length + 1) ^ k := by
    have h : 1 ≤ (x.length + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    calc c * (x.length + 1) ^ k + 1 ≤ c * (x.length + 1) ^ k + (x.length + 1) ^ k := by omega
      _ = (c + 1) * (x.length + 1) ^ k := by ring
  have h4 : (c * (x.length + 1) ^ k + 1) ^ 3 ≤ (c + 1) ^ 3 * (x.length + 1) ^ (3 * k) := by
    calc (c * (x.length + 1) ^ k + 1) ^ 3 ≤ ((c + 1) * (x.length + 1) ^ k) ^ 3 :=
          Nat.pow_le_pow_left h3 3
      _ = (c + 1) ^ 3 * (x.length + 1) ^ (3 * k) := by rw [mul_pow, ← pow_mul, mul_comm k 3]
  calc (reduction M c k x).length
      ≤ (M.numStates ^ 2 + 5 * M.transList.length + 22) *
          (c * (x.length + 1) ^ k + 1) ^ 3 := by rw [h1]; exact h2
    _ ≤ (M.numStates ^ 2 + 5 * M.transList.length + 22) *
          ((c + 1) ^ 3 * (x.length + 1) ^ (3 * k)) := Nat.mul_le_mul_left _ h4
    _ = (M.numStates ^ 2 + 5 * M.transList.length + 22) * (c + 1) ^ 3 *
          (x.length + 1) ^ (3 * k) := by ring

/-- **Cook–Levin: SAT is `NP`-hard.**

Every language `L` in `NP` (i.e. accepted by a nondeterministic Turing machine within a
polynomial number of steps) reduces to `SATLang` (the satisfiable CNF formulas): `x ∈ L`
if and only if the CNF formula `reduction M c k x` is satisfiable, and that formula has
polynomially many clauses in the length of `x`.

The reduction is not merely asserted to exist: it is the explicit, computable tableau
construction `Frontier.reduction`.  (An unrestricted existential `∃ f, ∀ x, x ∈ L ↔
Satisfiable (f x)` would be vacuous, since classically one could take `f x` to be `[]` or
`[[]]` according to whether `x ∈ L`.) -/
