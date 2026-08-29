/-
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Time Hierarchy

A diagonalization proof that more time gives strictly more languages.
-/

open Nat.Partrec Nat.Partrec.Code Denumerable

namespace CS

/-- A *language* is a decision problem on the natural numbers, i.e. a map `ℕ → Bool`.

`TIME t` is the class of languages that some program (a `Nat.Partrec.Code`) decides
within `t x` steps on input `x`, where "steps" are measured by Mathlib's step-indexed
evaluator `Nat.Partrec.Code.evaln`: `evaln k c x` runs the program `c` on input `x`
with fuel `k`, returning `none` if the fuel runs out. -/

theorem empty_mem_TIME : (fun _ => false) ∈ TIME (fun x => x + 1) :=
  ⟨Code.zero, fun x => by simp [evaln]⟩

/-- **Time hierarchy theorem.**  For every computable time bound `t` there is a larger time
bound `T` such that strictly more languages are decidable in time `T` than in time `t`.
The witness separating the two classes is the diagonal language `CS.diag t`. -/
