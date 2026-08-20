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

theorem Lang_mem_NPClass (B : Oracle) : Lang B ∈ NPClass B := by
  have hcost : ∀ x w : Str, 6 * x.length + 7 ≤ pb 2 (x.length + w.length) := by
    intro x w
    have h1 : 6 * x.length + 7 ≤ (x.length + 2) ^ 3 := by nlinarith [sq_nonneg x.length]
    exact le_trans h1 (Nat.pow_le_pow_left (by omega) 3)
  refine ⟨chkProg, 2, ?_, ?_⟩
  · intro x w
    obtain ⟨st', c, hc, hex, -⟩ := chkProg_exec B x w
    unfold Halts
    rw [hex.run_of_le (by rw [hc]; exact hcost x w)]
  · intro x
    rw [Lang_eq_true]
    constructor
    · rintro ⟨u, hu, hBu⟩
      obtain ⟨st', c, hc, hex, hout⟩ := chkProg_exec B x u
      refine ⟨u, ?_, ?_⟩
      · rw [hu]
        calc x.length ≤ (x.length + 2) ^ 1 := by simp
          _ ≤ pb 2 x.length := Nat.pow_le_pow_right (by omega) (by omega)
      · unfold Acc
        rw [hex.run_of_le (by rw [hc]; exact hcost x u)]
        refine ⟨rfl, ?_⟩
        show st'.regs 2 ≠ []
        rw [hout, ← hu, padTake_self, if_pos hBu]
        simp
    · rintro ⟨w, -, hAcc⟩
      obtain ⟨st', c, hc, hex, hout⟩ := chkProg_exec B x w
      have h2 := hAcc.2
      rw [hex.run_of_le (by rw [hc]; exact hcost x w)] at h2
      have h3 : st'.regs 2 ≠ [] := h2
      rw [hout] at h3
      by_cases hB : B (padTake x.length w) = true
      · exact ⟨padTake x.length w, by simp, hB⟩
      · simp [hB] at h3

end CS

