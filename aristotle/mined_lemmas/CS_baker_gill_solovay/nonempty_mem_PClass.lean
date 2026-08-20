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

theorem nonempty_mem_PClass (O : Oracle) : (fun x : Str => decide (x ≠ [])) ∈ PClass O := by
  have key : ∀ x : Str, ∃ st' : St,
      Exec O (Stmt.ifNE 0 (Stmt.pushC 2 true) Stmt.skip) (initSt x []) st' 2 ∧
        (st'.regs 2 ≠ [] ↔ x ≠ []) := by
    intro x
    by_cases hx : x = []
    · refine ⟨initSt x [], Exec.ifNE_neg (by simp [hx]) (Exec.skip O _), ?_⟩
      simp [hx, initSt_regs_other]
    · refine ⟨(initSt x []).setReg 2 (true :: (initSt x []).regs 2),
        Exec.ifNE_pos (by simpa using hx) (Exec.pushC O _ 2 true), ?_⟩
      simp [hx]
  refine ⟨Stmt.ifNE 0 (Stmt.pushC 2 true) Stmt.skip, 0, ?_, ?_⟩
  · intro x
    obtain ⟨st', hex, -⟩ := key x
    unfold Halts
    rw [hex.run_of_le (two_le_pb 0 x.length)]
  · intro x
    obtain ⟨st', hex, hiff⟩ := key x
    unfold Acc
    rw [hex.run_of_le (two_le_pb 0 x.length)]
    simp [hiff]

/-- The program which, on input `x`, writes the query string `0^j 1 0^m 1 x` (with
`m = (|x|+2)^d`) into the query register and asks the oracle about it, storing the answer
in the output register 2. -/
