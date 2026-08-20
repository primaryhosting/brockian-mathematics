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

theorem copyToQ_exec (O : Oracle) (i : ℕ) : ∀ (v : Str) (st : St), st.regs i = v →
    Exec O (copyToQ i) st
      { st with regs := Function.update st.regs i [], q := st.q ++ v } (4 * v.length + 1) := by
  intro v
  induction v with
  | nil =>
    intro st hst
    have h : ({ st with regs := Function.update st.regs i [], q := st.q ++ [] } : St) = st := by
      have : Function.update st.regs i [] = st.regs := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [hst]
        · simp [Function.update_of_ne hj]
      simp [this]
    rw [h]
    simpa using Exec.while_done (O := O) (body := Stmt.seq (Stmt.pushQ i) (Stmt.pop i)) (by rw [hst])
  | cons b r ih =>
    intro st hst
    have hne : st.regs i ≠ [] := by rw [hst]; simp
    -- body
    have h1 : Exec O (Stmt.pushQ i) st { st with q := st.q ++ [b] } 1 := by
      have := Exec.pushQ O st i
      rwa [hst] at this
    have h2 := Exec.pop O { st with q := st.q ++ [b] } i
    have hbody := Exec.seq h1 h2
    set st1 : St := (({ st with q := st.q ++ [b] } : St).setReg i
      ((({ st with q := st.q ++ [b] } : St)).regs i).tail) with hst1
    have hst1r : st1.regs i = r := by
      simp [hst1, St.setReg, hst]
    have hih := ih st1 hst1r
    have hres : ({ st1 with regs := Function.update st1.regs i [], q := st1.q ++ r } : St)
        = { st with regs := Function.update st.regs i [], q := st.q ++ (b :: r) } := by
      have hregs : Function.update st1.regs i [] = Function.update st.regs i [] := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hst1, St.setReg, Function.update_of_ne hj]
      have hq : st1.q ++ r = st.q ++ (b :: r) := by
        simp [hst1, St.setReg]
      simp only [hst1] at *
      exact St.mk.injEq .. ▸ ⟨hregs, hq, rfl⟩
    rw [hres] at hih
    have := Exec.while_step hne hbody hih
    convert this using 2
    simp
    omega

/-- `padProg d` appends `L ^ d` zeros to the query register, where `L` is the length of
register 9.  Registers `10, …, 9 + d` are used as loop counters. -/
