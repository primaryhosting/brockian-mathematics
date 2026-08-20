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

theorem Astep_congr {O₁ O₂ : Oracle} (s : Str)
    (h : ∀ t : Str, t.length < s.length → O₁ t = O₂ t) : Astep O₁ s = Astep O₂ s := by
  unfold Astep
  cases hd : decodeQ s with
  | none => rfl
  | some p =>
    simp only
    set k := (Nat.unpair p.1).2 with hk
    set M := progOfNat (Nat.unpair p.1).1 with hM
    set x := p.2 with hx
    by_cases hg : pb k (x.length + pb k x.length) < s.length
    · simp only [hg, if_true]
      refine decide_eq_decide.mpr ?_
      have hagree : ∀ u : Str, u.length ≤ pb k (x.length + pb k x.length) → O₁ u = O₂ u := by
        intro u hu
        exact h u (by omega)
      have key : ∀ w : Str, w.length ≤ pb k x.length →
          (Acc M O₁ x w (pb k (x.length + w.length)) ↔ Acc M O₂ x w (pb k (x.length + w.length))) := by
        intro w hw
        have hT : pb k (x.length + w.length) ≤ pb k (x.length + pb k x.length) :=
          pb_mono_right (by omega)
        have hrun := run_congr_of_le O₁ O₂ (pb k (x.length + pb k x.length)) hagree
          (pb k (x.length + w.length)) ([M], initSt x w) (by simpa using hT)
        unfold Acc
        rw [hrun]
      constructor
      · rintro ⟨w, hw, hacc⟩
        exact ⟨w, hw, (key w hw).mp hacc⟩
      · rintro ⟨w, hw, hacc⟩
        exact ⟨w, hw, (key w hw).mpr hacc⟩
    · simp [hg]

/-- `Aupto n` decides `A` correctly on all strings of length `< n`. -/
