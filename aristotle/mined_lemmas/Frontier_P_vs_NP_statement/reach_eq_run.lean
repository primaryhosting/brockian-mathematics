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

theorem reach_eq_run {t : ℕ} {c c' : Conf M.Q} (h : M.toNTM.reach t c c') : c' = M.run c t := by
  induction t generalizing c with
  | zero => simpa [run] using h
  | succ t ih =>
      obtain ⟨d, hd, hrest⟩ := h
      obtain ⟨-, rfl⟩ := toNTM_stepRel_iff.mp hd
      simpa [run] using ih hrest

end DTM

/-- Every polynomial-time decidable language is accepted by a polynomial-time
nondeterministic machine. -/
