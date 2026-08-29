import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file gives a complete, self-contained formalization of the statement `P ≠ NP`.
(Lean 4 requires every `import` to come before any other command, including
module documentation, so the header block above sits just after the single
`import Mathlib` line.)

Everything is built from scratch:

* a deterministic single-tape Turing machine model (`Frontier.DTM`) with a
  two-way infinite tape indexed by `ℤ`, tape alphabet `Option Bool`
  (`none` = blank), distinguished `accept` and `reject` states which are
  absorbing, and a total one-step transition function;
* a nondeterministic machine model (`Frontier.NTM`) whose transitions form a
  relation;
* time-bounded computation (`Frontier.DTM.run`, `Frontier.NTM.ReachIn`) and
  polynomial time bounds (`Frontier.IsPolyBound`);
* the classes `Frontier.P` and `Frontier.NP` of languages over `{0,1}`;
* polynomial-time computable functions, polynomial-time many-one reducibility
  `≤p`, NP-hardness and NP-completeness;
* the statement itself, `Frontier.P_vs_NP_statement : Prop`, namely `P ≠ NP`.

Some sanity results are proved: `P ⊆ NP`, the reformulation of the statement as
"some NP language is not in P", reflexivity of `≤p`, and the membership of the
two trivial languages in `P` (so that the classes are not empty).

The statement `P ≠ NP` itself is, of course, the famous open problem and is not
proved here.
-/

namespace Frontier

/-! ## Words and languages -/

/-- A word is a finite binary string. -/
abbrev Word := List Bool

/-- A language is a set of binary strings. -/
abbrev Language := Set Word

/-- Tape symbols: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym := Option Bool

/-! ## Configurations -/

/-- A head movement. -/
inductive Move where
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- The effect of a head movement on a (two-way infinite) tape position. -/

theorem swap_run (M : DTM) (x : Word) (k : ℕ) : M.swap.run x k = M.run x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 : M.swap.run x (k + 1) = M.swap.stepCfg (M.swap.run x k) := by
        simp [DTM.run, Function.iterate_succ_apply']
      have h2 : M.run x (k + 1) = M.stepCfg (M.run x k) := by
        simp [DTM.run, Function.iterate_succ_apply']
      rw [h1, h2, ih, swap_stepCfg]

/-- The class `P` is closed under complementation. -/
