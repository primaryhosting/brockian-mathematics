/-
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file gives a self-contained formalization of the classes `P` and `NP` of languages
over the binary alphabet, in terms of time-bounded (deterministic and nondeterministic)
Turing machines, together with polynomial-time many-one reducibility, NP-hardness and
NP-completeness.

The target theorem `Frontier.P_vs_NP_statement` records the precise statement of the
P vs NP problem together with the facts about it that are provable outright:

* `P ⊆ NP`;
* `P ≠ NP` is equivalent to the existence of a language in `NP` which is not in `P`;
* if some NP-complete language fails to be in `P`, then `P ≠ NP`.

(The truth value of `P ≠ NP` itself is of course not settled here.)
-/

namespace Frontier

/-- Tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym : Type := Option Bool

/-- A word is a finite binary string. -/
abbrev Word : Type := List Bool

/-- A language is a set of binary strings. -/
abbrev Language : Type := Set Word

/-- A tape is a bi-infinite sequence of symbols. -/
abbrev Tape : Type := ℤ → Sym

/-- The initial tape holding the input `x` in cells `0, 1, …, |x| - 1`, blank elsewhere. -/

theorem exists_reach_run (c : Conf M.Q) (t : ℕ) : ∃ s ≤ t, M.toNTM.reach s c (M.run c t) := by
  induction t with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ t ih =>
      obtain ⟨s, hs, hr⟩ := ih
      by_cases h : (M.out (M.run c t).1).isSome
      · refine ⟨s, by omega, ?_⟩
        rw [run_succ, stepc, if_pos h]
        exact hr
      · refine ⟨s + 1, by omega, ?_⟩
        rw [run_succ]
        exact reach_snoc hr (toNTM_stepRel_iff.mpr ⟨h, rfl⟩)

