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

theorem buildQ_exec (O : Oracle) : ∀ (v : Str) (st : St), st.regs 3 = v →
    ∃ st' : St, Exec O buildQ st st' (6 * v.length + 1) ∧
      st'.q = st.q ++ padTake v.length (st.regs 4) ∧ st'.log = st.log := by
  intro v
  induction v with
  | nil =>
    intro st hst
    refine ⟨st, ?_, by simp [padTake], rfl⟩
    have hdone := Exec.while_done (O := O) (i := 3)
      (body := Stmt.seq (Stmt.pushQ 4) (Stmt.seq (Stmt.pop 4) (Stmt.pop 3))) (by rw [hst])
    simpa [buildQ] using hdone
  | cons b r ih =>
    intro st hst
    have hne : st.regs 3 ≠ [] := by rw [hst]; simp
    have e1 := Exec.pushQ O st 4
    set s1 : St := { st with q := st.q ++ [(st.regs 4).headD false] } with hs1
    have e2 := Exec.pop O s1 4
    set s2 : St := s1.setReg 4 (s1.regs 4).tail with hs2
    have e3 := Exec.pop O s2 3
    set s3 : St := s2.setReg 3 (s2.regs 3).tail with hs3
    have hs3r3 : s3.regs 3 = r := by
      rw [hs3, St.setReg_same, hs2, St.setReg_ne _ (by omega)]
      show (st.regs 3).tail = r
      rw [hst]; rfl
    have hs3r4 : s3.regs 4 = (st.regs 4).tail := by
      rw [hs3, St.setReg_ne _ (by omega), hs2, St.setReg_same]
    have hs3q : s3.q = st.q ++ [(st.regs 4).headD false] := rfl
    have hs3log : s3.log = st.log := rfl
    obtain ⟨st', hex, hq, hlog⟩ := ih s3 hs3r3
    refine ⟨st', ?_, ?_, by rw [hlog, hs3log]⟩
    · have hbody := Exec.seq e1 (Exec.seq e2 e3)
      have := Exec.while_step hne hbody hex
      convert this using 2
      simp
      omega
    · rw [hq, hs3q, hs3r4]
      show _ = st.q ++ padTake (r.length + 1) (st.regs 4)
      simp [padTake]

/-- The nondeterministic machine for `Lang B`. -/
