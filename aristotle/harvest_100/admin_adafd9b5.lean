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
def StepModel.DTIME (M : StepModel) (t : Nat → Nat) (L : Lang) : Prop :=
  ∃ e, ∀ x, M.run e x (t x) = some (L x)

/-- The diagonal language for the time bound `t`: on input `x`, simulate the
program with index `x` on input `x` for `t x` steps and output the opposite
answer (outputting `false` if that simulation has not halted). -/
def StepModel.diag (M : StepModel) (t : Nat → Nat) : Lang :=
  fun x => match M.run x x (t x) with
    | some b => !b
    | none => false

/-- Larger time bounds decide at least as many languages. -/
theorem StepModel.DTIME_mono (M : StepModel) {t T : Nat → Nat} (hle : ∀ x, t x ≤ T x)
    {L : Lang} (hL : M.DTIME t L) : M.DTIME T L := by
  obtain ⟨e, he⟩ := hL
  exact ⟨e, fun x => M.mono (hle x) (he x)⟩

/-- Diagonalization: the diagonal language for the bound `t` is not decided by
any program of the model within `t` steps. -/
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
theorem time_hierarchy (M : StepModel) (t T : Nat → Nat)
    (hle : ∀ x, t x ≤ T x)
    (hsim : ∃ d, ∀ x, M.run d x (T x) = some (M.diag t x)) :
    (∀ L, M.DTIME t L → M.DTIME T L) ∧ ∃ L, M.DTIME T L ∧ ¬ M.DTIME t L := by
  refine ⟨fun _ hL => M.DTIME_mono hle hL, M.diag t, hsim, ?_⟩
  exact M.diag_not_mem_DTIME t

/-- The hypotheses of `CS.time_hierarchy` are satisfiable, so the theorem is not
vacuous: here is a (degenerate) model in which no program answers within one
step, while some program answers `false` after two steps. -/
example : ∃ (M : StepModel) (t T : Nat → Nat),
    (∀ x, t x ≤ T x) ∧ (∃ d, ∀ x, M.run d x (T x) = some (M.diag t x)) ∧
    ((∀ L, M.DTIME t L → M.DTIME T L) ∧ ∃ L, M.DTIME T L ∧ ¬ M.DTIME t L) := by
  refine ⟨⟨fun _ _ n => if 2 ≤ n then some false else none, ?_⟩,
    (fun _ => 1), (fun _ => 2), fun _ => Nat.le_succ 1, ⟨0, ?_⟩, ?_⟩
  · intro e x n m b hnm h
    by_cases hn : 2 ≤ n
    · have hm : 2 ≤ m := Nat.le_trans hn hnm
      simp only [if_pos hn] at h
      simp [if_pos hm, h]
    · simp [hn] at h
  · intro x
    simp [StepModel.diag]
  · refine time_hierarchy _ _ _ (fun _ => Nat.le_succ 1) ⟨0, ?_⟩
    intro x
    simp [StepModel.diag]

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

