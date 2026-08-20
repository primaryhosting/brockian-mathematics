import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` statements to precede every other command, including module
docstrings, so the required header comment appears immediately after `import Mathlib`.
-/

open Nat.Partrec Nat.Partrec.Code Denumerable Encodable

namespace CS

/-- A language is a decision predicate on (natural-number encoded) inputs. -/
abbrev Lang := ℕ → Bool

/-- `TIME t` is the class of languages decided by some partial-recursive code within
`t n` steps of the step-indexed evaluator `Nat.Partrec.Code.evaln` on input `n`. -/

theorem constFalse_mem_TIME : (fun _ => false) ∈ TIME (fun n => n + 1) :=
  ⟨Code.zero, fun n => by simp [Nat.Partrec.Code.evaln]⟩

/-- The diagonal language for the time bound `t`: on input `n`, run the `n`-th code on `n`
for `t n` steps and output the opposite answer. -/
