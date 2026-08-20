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

theorem exists_unqueried (Lg : List Str) (n : ℕ) (h : Lg.length < 2 ^ n) :
    ∃ u : Str, u.length = n ∧ u ∉ Lg := by
  by_contra hcon
  push_neg at hcon
  classical
  set S : Finset Str := (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)
    with hS
  have hinj : Function.Injective (fun f : Fin n → Bool => List.ofFn f) := by
    intro f g hfg
    exact List.ofFn_injective hfg
  have hcard : S.card = 2 ^ n := by
    rw [hS, Finset.card_image_of_injective _ hinj]
    simp
  have hsub : S ⊆ Lg.toFinset := by
    intro u hu
    rw [hS] at hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨f, rfl⟩ := hu
    exact List.mem_toFinset.mpr (hcon _ (by simp))
  have h1 := Finset.card_le_card hsub
  have h2 : Lg.toFinset.card ≤ Lg.length := Lg.toFinset_card_le
  omega

open Classical in
/-- A string of length `n` which does not occur in the list `Lg`. -/
