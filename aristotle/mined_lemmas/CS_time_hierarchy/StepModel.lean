/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: this file is deliberately self-contained (no `import` line), because a
-- module docstring such as the header above must precede any import.  Only
-- Lean 4 core is used.

set_option autoImplicit false

namespace CS

/-- A step-indexed abstract model of computation.

`run e x n` is the outcome of running the program with index `e` on the input `x`
for `n` steps: `none` means "has not produced an answer yet", `some b` means
"has halted with output `b`".  The only structural requirement is that answers
are persistent: once a program has produced an answer, running it longer
produces the same answer. -/
structure StepModel where
  /-- `run e x n` = output of program `e` on input `x` after `n` steps. -/
  run : Nat → Nat → Nat → Option Bool
  /-- Answers are persistent when the machine is run longer. -/
  mono : ∀ {e x n m b}, n ≤ m → run e x n = some b → run e x m = some b

/-- A language is a decision problem on (encoded) inputs. -/
abbrev Lang := Nat → Bool

/-- `M.DTIME t L` says that the language `L` is decided by some program of the
model `M` within `t x` steps on every input `x`. -/

theorem StepModel.diag_not_mem_DTIME (M : StepModel) (t : Nat → Nat) :
    ¬ M.DTIME t (M.diag t) := by
  rintro ⟨e, he⟩
  -- Evaluate the diagonal language at its own program index.
  have hd : M.diag t e = match M.run e e (t e) with
      | some b => !b
      | none => false := rfl
  rw [he e] at hd
  -- Split on the value of the diagonal language at `e`; both branches are absurd.
  cases hb : M.diag t e with
  | false => rw [hb] at hd; simp at hd
  | true => rw [hb] at hd; simp at hd

/-- **Time hierarchy theorem.**

Fix a step-indexed model of computation `M` and two time bounds `t ≤ T`.
If the model admits a program that, within `T` steps, computes the diagonal
language obtained by simulating `t`-step computations (this is the "efficient
universal simulation" ingredient: simulating `t` steps costs at most `T` steps),
then strictly more languages are decidable in time `T` than in time `t`:
every `t`-time language is a `T`-time language, and some `T`-time language is
not a `t`-time language. -/
