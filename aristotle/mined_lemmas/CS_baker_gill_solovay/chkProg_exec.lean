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

theorem chkProg_exec (O : Oracle) (x w : Str) :
    ∃ (st' : St) (c : ℕ), c = 6 * x.length + 7 ∧
      Exec O chkProg (initSt x w) st' c ∧
      st'.regs 2 = (if O (padTake x.length w) then [true] else []) := by
  have e1 := Exec.copy O (initSt x w) 3 0
  set s1 : St := (initSt x w).setReg 3 ((initSt x w).regs 0) with hs1
  have e2 := Exec.copy O s1 4 1
  set s2 : St := s1.setReg 4 (s1.regs 1) with hs2
  have hs2r3 : s2.regs 3 = x := by
    rw [hs2, St.setReg_ne _ (by omega), hs1, St.setReg_same]
    simp
  have hs2r4 : s2.regs 4 = w := by
    rw [hs2, St.setReg_same, hs1, St.setReg_ne _ (by omega)]
    simp
  have hs2q : s2.q = [] := rfl
  obtain ⟨s3, e3, hq3, -⟩ := buildQ_exec O x s2 hs2r3
  rw [hs2q, hs2r4] at hq3
  have e4 := Exec.query O s3 2
  refine ⟨_, _, ?_, Exec.seq e1 (Exec.seq e2 (Exec.seq e3 e4)), ?_⟩
  · omega
  · show Function.update s3.regs 2 (if O s3.q then [true] else []) 2 = _
    rw [hq3]
    simp

/-- The language `{ x | ∃ u, |u| = |x| ∧ u ∈ B }`. -/
