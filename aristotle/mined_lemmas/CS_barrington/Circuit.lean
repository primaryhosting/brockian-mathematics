/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

We formalise Barrington's theorem: the class of Boolean function families computed by
logarithmic-depth fan-in-two Boolean circuits (`NC¹`) coincides with the class of families
computed by polynomial-length width-`5` permutation branching programs.

* `CS.Barrington.Circuit` : fan-in two Boolean circuits over `{¬, ∧, ∨}` and constants.
* `CS.Barrington.Instr`, `CS.Barrington.run` : width-5 permutation branching programs,
  i.e. lists of instructions, each of which multiplies the running value in `S₅` by a
  permutation depending on (at most) one input bit.
* `CS.Barrington.NC1` and `CS.Barrington.W5BP` : the two classes.
* `CS.barrington` : the two classes are equal.
-/

namespace CS
namespace Barrington

open Equiv

/-- The symmetric group on five points. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-! ### Boolean circuits -/

/-- Fan-in two Boolean circuits (formulas) on `n` inputs. -/
inductive Circuit (n : ℕ) where
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

/-- The Boolean function computed by a circuit. -/

def Circuit.depth {n : ℕ} : Circuit n → ℕ
  | .var _ => 0
  | .const _ => 0
  | .not c => c.depth + 1
  | .and c d => max c.depth d.depth + 1
  | .or c d => max c.depth d.depth + 1

/-! ### Width-5 permutation branching programs -/

/-- An instruction of a width-5 permutation branching program: either a fixed permutation,
or a permutation depending on the value of one input bit. -/
inductive Instr (n : ℕ) where
  | const : Perm5 → Instr n
  | query : Fin n → Perm5 → Perm5 → Instr n

/-- The permutation contributed by an instruction on a given input. -/
