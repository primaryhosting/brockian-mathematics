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

theorem Lang_not_mem_PClass_B : Lang B ∉ PClass B := by
  rintro ⟨M, k, -, hacc⟩
  classical
  set i := Nat.pair (natOfProg M) k with hi
  have hP : stageProg i = M := by simp [stageProg, hi]
  have hK : stageK i = k := by simp [stageK, hi]
  set n := stageN i with hn
  set T := stageT i with hT
  set x := stageX i with hx
  have hxlen : x.length = n := by simp [hx, stageX, hn]
  have hTpb : T = pb k x.length := by rw [hT, stageT, hK, hxlen, hn]
  -- the run with the finite oracle and the run with `B` coincide
  have hlog : ∀ s ∈ (run (stage i).2 T ([M], initSt x [])).2.log, (stage i).2 s = B s := by
    intro s hs
    have hslen : s.length ≤ T := by
      refine log_mem_length_le (stage i).2 T T ([M], initSt x []) ?_ ?_ s hs
      · simp
      · simp
    have hsle : s.length ≤ (stage (i + 1)).1 := by
      rw [stage_succ_fst]
      omega
    have hne : s ≠ stageU i := by
      intro hcon
      have := (stageU_spec i).2
      rw [← hcon, hP, ← hT, ← hx] at this
      exact this hs
    rw [B_eq_stage (i + 1) s hsle, stage_succ_snd_of_ne hne]
  have hruneq : run B T ([M], initSt x []) = run (stage i).2 T ([M], initSt x []) :=
    run_congr_of_log (stage i).2 B T _ hlog
  have hAccIff : Acc M B x [] T ↔ Acc M (stage i).2 x [] T := by
    unfold Acc
    rw [hruneq]
  by_cases hA : Acc M (stage i).2 x [] T
  · -- the machine accepts, but no string of length `n` is in `B`
    have hAccB : Acc M B x [] (pb k x.length) := by
      rw [← hTpb]
      exact hAccIff.mpr hA
    obtain ⟨u, hu, hBu⟩ := Lang_eq_true.mp ((hacc x).mpr hAccB)
    have hstage : stage (i + 1) = (max T n, (stage i).2) := by
      rw [stage_succ_of_acc (by rw [hP, ← hx, ← hT]; exact hA), ← hT, ← hn]
    have hule : u.length ≤ (stage (i + 1)).1 := by
      rw [hstage]
      simp only
      omega
    have hBu' : (stage (i + 1)).2 u = true := by rw [← B_eq_stage (i + 1) u hule]; exact hBu
    rw [hstage] at hBu'
    simp only at hBu'
    have := stage_len_le i u hBu'
    have h2 := stageN_gt i
    omega
  · -- the machine rejects, but the fresh string of length `n` is in `B`
    have hstage : stage (i + 1) =
        (max T n, fun s => (stage i).2 s || decide (s = stageU i)) := by
      rw [stage_succ_of_not_acc (by rw [hP, ← hx, ← hT]; exact hA), ← hT, ← hn]
    have hBu : B (stageU i) = true := by
      refine B_eq_true.mpr ⟨i + 1, ?_⟩
      rw [hstage]
      simp
    have hlen : (stageU i).length = x.length := by rw [(stageU_spec i).1, hxlen, hn]
    have : Lang B x = true := Lang_eq_true.mpr ⟨stageU i, hlen, hBu⟩
    have hAccB := (hacc x).mp this
    rw [← hTpb] at hAccB
    exact hA (hAccIff.mp hAccB)

