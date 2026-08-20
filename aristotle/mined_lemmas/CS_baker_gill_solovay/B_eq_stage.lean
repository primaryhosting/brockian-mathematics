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

theorem B_eq_stage (a : ℕ) (s : Str) (h : s.length ≤ (stage a).1) : B s = (stage a).2 s := by
  by_cases hst : (stage a).2 s = true
  · have : B s = true := B_eq_true.mpr ⟨a, hst⟩
    rw [this, hst]
  · have hfalse : B s = false := by
      by_contra hB
      have hBt : B s = true := by
        cases hb : B s
        · exact absurd hb hB
        · rfl
      obtain ⟨j, hj⟩ := B_eq_true.mp hBt
      -- show `s` is already in `stage a`
      have key : ∀ j : ℕ, (stage j).2 s = true → (stage a).2 s = true := by
        intro j
        induction j with
        | zero => intro h0; exact absurd h0 (by simp [stage])
        | succ n ihn =>
          intro hn
          rcases Nat.lt_or_ge n a with hna | hna
          · exact stage_snd_mono (by omega) hn
          · rcases stage_succ_snd_cases hn with h' | h'
            · exact ihn h'
            · exfalso
              have h1 : (stage a).1 ≤ (stage n).1 := stage_fst_mono hna
              have h2 : (stage n).1 < stageN n := stageN_gt n
              have h3 : s.length = stageN n := by rw [h', (stageU_spec n).1]
              omega
      exact absurd (key j hj) hst
    rw [hfalse]
    cases hb : (stage a).2 s
    · rfl
    · exact absurd hb hst

