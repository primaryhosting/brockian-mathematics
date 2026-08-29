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

theorem out_unique {c : Conf M.Q} {t₁ t₂ : ℕ} {b₁ b₂ : Bool}
    (h₁ : M.out (M.run c t₁).1 = some b₁) (h₂ : M.out (M.run c t₂).1 = some b₂) :
    b₁ = b₂ := by
  have e₁ : M.run c (t₁ + (max t₁ t₂ - t₁)) = M.run c t₁ :=
    run_of_halted (by rw [h₁]; simp) _
  have e₂ : M.run c (t₂ + (max t₁ t₂ - t₂)) = M.run c t₂ :=
    run_of_halted (by rw [h₂]; simp) _
  rw [show t₁ + (max t₁ t₂ - t₁) = max t₁ t₂ by omega] at e₁
  rw [show t₂ + (max t₁ t₂ - t₂) = max t₁ t₂ by omega] at e₂
  have : some b₁ = some b₂ := by rw [← h₁, ← h₂, ← e₁, ← e₂]
  simpa using this

end DTM

/-- The nondeterministic machine simulating a deterministic one. -/
