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

theorem simProg_exec (O : Oracle) (j d : ℕ) (x : Str) :
    ∃ (c : ℕ) (st' : St),
      c ≤ 2 * j + 4 * x.length + 18 + (x.length + 2 + 4) ^ (d + 1) ∧
      Exec O (simProg j d) (initSt x []) st' c ∧
      st'.regs 2 = (if O (encodeQ j ((x.length + 2) ^ d) x) then [true] else []) := by
  set n := x.length with hn
  -- step 1 : `regs 9 := x`
  have e1 := Exec.copy O (initSt x []) 9 0
  set s1 : St := (initSt x []).setReg 9 ((initSt x []).regs 0) with hs1
  have hs1q : s1.q = [] := rfl
  have hs1r0 : s1.regs 0 = x := by rw [hs1, St.setReg_ne _ (by omega)]; simp
  have hs1r9 : s1.regs 9 = x := by rw [hs1, St.setReg_same]; simp
  -- steps 2 and 3 : two zeros in front of register 9
  have e2 := Exec.pushC O s1 9 false
  set s2 : St := s1.setReg 9 (false :: s1.regs 9) with hs2
  have hs2q : s2.q = [] := hs1q
  have hs2r0 : s2.regs 0 = x := by rw [hs2, St.setReg_ne _ (by omega)]; exact hs1r0
  have hs2r9 : s2.regs 9 = false :: x := by rw [hs2, St.setReg_same, hs1r9]
  have e3 := Exec.pushC O s2 9 false
  set s3 : St := s2.setReg 9 (false :: s2.regs 9) with hs3
  have hs3q : s3.q = [] := hs2q
  have hs3r0 : s3.regs 0 = x := by rw [hs3, St.setReg_ne _ (by omega)]; exact hs2r0
  have hs3r9 : s3.regs 9 = false :: false :: x := by rw [hs3, St.setReg_same, hs2r9]
  -- step 4 : the constant prefix `0^j`
  have e4 := pushConstStr_exec O (List.replicate j false) s3
  set s4 : St := { s3 with q := s3.q ++ List.replicate j false } with hs4
  have hs4q : s4.q = List.replicate j false := by rw [hs4]; show s3.q ++ _ = _; rw [hs3q]; simp
  have hs4r0 : s4.regs 0 = x := hs3r0
  have hs4r9 : s4.regs 9 = false :: false :: x := hs3r9
  -- step 5 : the separator
  have e5 := Exec.pushQC O s4 true
  set s5 : St := { s4 with q := s4.q ++ [true] } with hs5
  have hs5q : s5.q = List.replicate j false ++ [true] := by
    rw [hs5]; show s4.q ++ _ = _; rw [hs4q]
  have hs5r0 : s5.regs 0 = x := hs4r0
  have hs5r9 : s5.regs 9 = false :: false :: x := hs4r9
  have hs5len : (s5.regs 9).length = n + 2 := by rw [hs5r9]; simp [hn]
  -- step 6 : the padding
  obtain ⟨c6, s6, hc6, e6, hq6, hr6, -⟩ := padProg_exec O d s5
  rw [hs5len] at hc6 hq6
  have hs6r0 : s6.regs 0 = x := by rw [hr6 0 (by omega)]; exact hs5r0
  have hs6q : s6.q = List.replicate j false ++ [true] ++ List.replicate ((n + 2) ^ d) false := by
    rw [hq6, hs5q]
  -- step 7 : the second separator
  have e7 := Exec.pushQC O s6 true
  set s7 : St := { s6 with q := s6.q ++ [true] } with hs7
  have hs7q : s7.q
      = List.replicate j false ++ [true] ++ List.replicate ((n + 2) ^ d) false ++ [true] := by
    rw [hs7]; show s6.q ++ _ = _; rw [hs6q]
  have hs7r0 : s7.regs 0 = x := hs6r0
  -- step 8 : copy the input into a scratch register
  have e8 := Exec.copy O s7 8 0
  set s8 : St := s7.setReg 8 (s7.regs 0) with hs8
  have hs8r8 : s8.regs 8 = x := by rw [hs8, St.setReg_same, hs7r0]
  have hs8q : s8.q
      = List.replicate j false ++ [true] ++ List.replicate ((n + 2) ^ d) false ++ [true] := hs7q
  -- step 9 : append the input to the query register
  have e9 := copyToQ_exec O 8 x s8 hs8r8
  set s9 : St := { s8 with regs := Function.update s8.regs 8 [], q := s8.q ++ x } with hs9
  have hs9q : s9.q = encodeQ j ((n + 2) ^ d) x := by
    rw [hs9]
    show s8.q ++ x = _
    rw [hs8q]
    simp [encodeQ]
  -- step 10 : the oracle call
  have e10 := Exec.query O s9 2
  refine ⟨_, _, ?_, Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq e4 (Exec.seq e5
      (Exec.seq e6 (Exec.seq e7 (Exec.seq e8 (Exec.seq e9 e10)))))))), ?_⟩
  · simp only [List.length_replicate, ← hn]
    generalize (n + 2 + 4) ^ (d + 1) = X at hc6 ⊢
    omega
  · show Function.update s9.regs 2 (if O s9.q then [true] else []) 2 = _
    rw [hs9q]
    simp

end CS

import Mathlib

/-!
# A concrete model of oracle computation

Strings are lists of booleans, an oracle is a boolean-valued function on strings.
Machines are programs of a small imperative language with registers holding strings
and a distinguished *query register* `q` which is filled one symbol at a time and is
emptied by each oracle call.  This convention guarantees the fundamental property

  *the length of every oracle query is bounded by the number of steps of the computation*

which is what makes the self-referential oracle of Baker-Gill-Solovay well defined.
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, given by its characteristic function. -/
abbrev Oracle := Str → Bool

/-- Programs. -/
inductive Stmt where
  /-- do nothing -/
  | skip : Stmt
  /-- sequential composition -/
  | seq : Stmt → Stmt → Stmt
  /-- `regs i := b :: regs i` -/
  | pushC : ℕ → Bool → Stmt
  /-- `regs i := (regs i).tail` -/
  | pop : ℕ → Stmt
  /-- `regs i := regs j` -/
  | copy : ℕ → ℕ → Stmt
  /-- append the first symbol of `regs i` to the query register -/
  | pushQ : ℕ → Stmt
  /-- append a constant symbol to the query register -/
  | pushQC : Bool → Stmt
  /-- ask the oracle about the contents of the query register, store the answer in
  `regs i` (as `[true]` or `[]`) and empty the query register -/
  | query : ℕ → Stmt
  /-- `while regs i ≠ [] do body` -/
  | whileNE : ℕ → Stmt → Stmt
  /-- `if regs i ≠ [] then a else b` -/
  | ifNE : ℕ → Stmt → Stmt → Stmt
  deriving Inhabited, DecidableEq

/-- Machine states: registers, the query register, and a log of all queries made. -/
structure St where
  regs : ℕ → Str
  q : Str
  log : List Str

/-- Configurations: a stack of statements still to be executed, and a state. -/
abbrev Cfg := List Stmt × St

/-- One computation step. A configuration with empty statement stack is halted. -/
