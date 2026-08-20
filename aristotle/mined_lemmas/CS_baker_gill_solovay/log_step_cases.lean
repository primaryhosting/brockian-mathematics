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

import RequestProject.BGS.OracleA
import RequestProject.BGS.OracleB

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header block above is placed directly after the `import` lines, because Lean 4
requires `import` commands to be the very first commands of a module.)

## Summary of the development

Everything is developed from scratch in this project:

* `CS.Stmt`, `CS.step`, `CS.run` (`RequestProject/BGS/Model.lean`): a concrete model of
  oracle computation.  Programs are statements of a small imperative language with
  string registers; oracle queries are built one symbol at a time in a dedicated query
  register, so that *the length of a query never exceeds the number of steps performed*.
* `CS.PClass`, `CS.NPClass` (`RequestProject/BGS/Classes.lean`): the relativized classes
  `P^O` and `NP^O`, defined with the polynomial bounds `pb k n = (n+2)^(k+1)`.
* `CS.A` (`RequestProject/BGS/OracleA.lean`): a self-referential oracle answering
  `NP^A`-questions in one query; well defined by recursion on the length of the queried
  string.  It satisfies `P^A = NP^A`.
* `CS.B` (`RequestProject/BGS/OracleB.lean`): an oracle built by stages, diagonalizing
  against every polynomial time oracle machine, for which the language
  `CS.Lang B = { x | ∃ u, |u| = |x| ∧ u ∈ B }` lies in `NP^B` but not in `P^B`.
-/

namespace CS

/-- **Baker–Gill–Solovay**: there is an oracle `A` with `P^A = NP^A` and an oracle `B`
with `P^B ≠ NP^B`; hence no relativizing proof can settle the `P` versus `NP` question. -/

theorem log_step_cases (O : Oracle) (c : Cfg) :
    (step O c).2.log = c.2.log ∨ (step O c).2.log = c.2.log ++ [c.2.q] := by
  obtain ⟨l, st⟩ := c
  match l with
  | [] => exact Or.inl rfl
  | Stmt.skip :: r => exact Or.inl rfl
  | Stmt.seq a b :: r => exact Or.inl rfl
  | Stmt.pushC i b :: r => exact Or.inl rfl
  | Stmt.pop i :: r => exact Or.inl rfl
  | Stmt.copy i j :: r => exact Or.inl rfl
  | Stmt.pushQ i :: r => exact Or.inl rfl
  | Stmt.pushQC b :: r => exact Or.inl rfl
  | Stmt.query i :: r => exact Or.inr rfl
  | Stmt.whileNE i body :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]
  | Stmt.ifNE i a b :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]

/-- Every string queried during a run of at most `N` steps has length at most `N`. -/
