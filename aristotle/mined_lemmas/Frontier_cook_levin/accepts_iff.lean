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

theorem accepts_iff (x : List Bool) (T : ℕ) :
    M.Accepts x T ↔ ∃ t, t ≤ T ∧ ∃ r : ℕ → Cfg, r 0 = M.init x ∧
      (∀ s, s < t → M.Next (r s) (r (s + 1))) ∧ (r t).state = M.accept := by
  constructor
  · rintro ⟨r, hr0, hstep, t, htT, hacc⟩
    exact ⟨t, htT, r, hr0, fun s hs => hstep s (lt_of_lt_of_le hs htT), hacc⟩
  · rintro ⟨t, htT, r, hr0, hstep, hacc⟩
    have hstate : (r t).state < M.numStates := M.state_lt_of_run hr0 hstep t le_rfl
    have hiter : ∀ n, (M.someNext^[n] (r t)).state < M.numStates := by
      intro n
      induction n with
      | zero => simpa using hstate
      | succ m ih => rw [Function.iterate_succ_apply']; exact M.someNext_state_lt ih
    refine ⟨fun s => if s ≤ t then r s else M.someNext^[s - t] (r t), by simp [hr0], ?_,
      t, htT, by simp [hacc]⟩
    intro s _
    by_cases hs : s + 1 ≤ t
    · simp only [if_pos hs, if_pos (by omega : s ≤ t)]
      exact hstep s (by omega)
    · by_cases hs' : s ≤ t
      · have hst : s = t := by omega
        subst hst
        simp only [if_pos le_rfl, if_neg hs]
        have : s + 1 - s = 1 := by omega
        rw [this]
        simpa using M.next_someNext hstate
      · simp only [if_neg hs, if_neg hs']
        have h1 : s + 1 - t = (s - t) + 1 := by omega
        rw [h1, Function.iterate_succ_apply']
        exact M.next_someNext (hiter _)

end NTM

/-- A language is a set of bit strings. -/
abbrev Language := Set (List Bool)

/-- `L ∈ NP`: some nondeterministic Turing machine accepts exactly `L`, within a
polynomial number of steps. -/
