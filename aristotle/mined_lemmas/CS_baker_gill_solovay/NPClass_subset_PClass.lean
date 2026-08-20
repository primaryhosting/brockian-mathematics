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

theorem NPClass_subset_PClass : NPClass A ⊆ PClass A := by
  rintro L ⟨M, k, hhalt, hacc⟩
  classical
  refine ⟨simProg (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)),
    2 * (Nat.pair (natOfProg M) k) + 3 * ((k + 3) * (k + 1)) + 21 + 1, ?_, ?_⟩
  · -- the simulating machine halts within the required time bound
    intro x
    obtain ⟨c, st', hc, hex, -⟩ :=
      simProg_exec A (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x
    have hb := le_trans hc (bound_aux (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x)
    unfold Halts
    rw [hex.run_of_le hb]
  · intro x
    obtain ⟨c, st', hc, hex, hout⟩ :=
      simProg_exec A (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x
    have hb := le_trans hc (bound_aux (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x)
    have hrun := hex.run_of_le hb
    have hpad := pad_big (Nat.pair (natOfProg M) k) k x
    rw [hacc x]
    constructor
    · intro hexists
      have hA : A (encodeQ (Nat.pair (natOfProg M) k) ((x.length + 2) ^ ((k + 3) * (k + 1))) x)
          = true := (A_encodeQ M k x _ hpad).mpr hexists
      unfold Acc
      rw [hrun]
      refine ⟨rfl, ?_⟩
      show st'.regs 2 ≠ []
      rw [hout, if_pos hA]
      simp
    · intro hAcc
      have h2 := hAcc.2
      rw [hrun] at h2
      have h3 : st'.regs 2 ≠ [] := h2
      rw [hout] at h3
      by_cases hA : A (encodeQ (Nat.pair (natOfProg M) k)
          ((x.length + 2) ^ ((k + 3) * (k + 1))) x) = true
      · exact (A_encodeQ M k x _ hpad).mp hA
      · simp [hA] at h3

/-- **Relativized collapse**: for the oracle `A`, `P^A = NP^A`. -/
