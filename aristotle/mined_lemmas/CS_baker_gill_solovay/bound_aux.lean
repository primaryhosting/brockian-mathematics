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

theorem bound_aux (j d : ℕ) (x : Str) :
    2 * j + 4 * x.length + 18 + (x.length + 2 + 4) ^ (d + 1)
      ≤ pb (2 * j + 3 * d + 21 + 1) x.length := by
  set n := x.length with hn
  set S := 2 * j + 3 * d + 21 with hS
  have hL2 : 2 ≤ n + 2 := by omega
  have hsq : (4:ℕ) ≤ (n + 2) ^ 2 := by nlinarith
  have hcube : (n + 2) ^ 3 = (n + 2) ^ 2 * (n + 2) := by ring
  have e1 : 2 * j ≤ (n + 2) ^ S :=
    le_trans (le_pow_base_two n (2 * j)) (Nat.pow_le_pow_right (by omega) (by omega))
  have e2 : 4 * n ≤ (n + 2) ^ S := by
    have h3 : 4 * n ≤ (n + 2) ^ 3 := by
      rw [hcube]; nlinarith
    exact le_trans h3 (Nat.pow_le_pow_right (by omega) (by omega))
  have e3 : 18 ≤ (n + 2) ^ S :=
    le_trans (le_pow_base_two n 18) (Nat.pow_le_pow_right (by omega) (by omega))
  have e4 : (n + 2 + 4) ^ (d + 1) ≤ (n + 2) ^ S := by
    have hbase : n + 2 + 4 ≤ (n + 2) ^ 3 := by rw [hcube]; nlinarith
    calc (n + 2 + 4) ^ (d + 1) ≤ ((n + 2) ^ 3) ^ (d + 1) := Nat.pow_le_pow_left hbase _
      _ = (n + 2) ^ (3 * (d + 1)) := by rw [← pow_mul]
      _ ≤ (n + 2) ^ S := Nat.pow_le_pow_right (by omega) (by omega)
  have hfinal : 4 * (n + 2) ^ S ≤ pb (S + 1) n := by
    show 4 * (n + 2) ^ S ≤ (n + 2) ^ (S + 1 + 1)
    calc 4 * (n + 2) ^ S ≤ (n + 2) ^ 2 * (n + 2) ^ S := Nat.mul_le_mul_right _ hsq
      _ = (n + 2) ^ (S + 2) := by ring
      _ = (n + 2) ^ (S + 1 + 1) := by ring_nf
  omega

