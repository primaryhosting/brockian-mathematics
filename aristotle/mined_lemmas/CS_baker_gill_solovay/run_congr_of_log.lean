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

theorem run_congr_of_log (O₁ O₂ : Oracle) :
    ∀ (t : ℕ) (c : Cfg), (∀ s ∈ (run O₁ t c).2.log, O₁ s = O₂ s) → run O₂ t c = run O₁ t c := by
  intro t
  induction t with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    rw [run_succ] at hc ⊢
    have hstep : step O₂ c = step O₁ c := by
      obtain ⟨l, st⟩ := c
      match l with
      | [] => rfl
      | Stmt.skip :: r => rfl
      | Stmt.seq a b :: r => rfl
      | Stmt.pushC i b :: r => rfl
      | Stmt.pop i :: r => rfl
      | Stmt.copy i j :: r => rfl
      | Stmt.pushQ i :: r => rfl
      | Stmt.pushQC b :: r => rfl
      | Stmt.query i :: r =>
          have hmem : st.q ∈ (run O₁ n (step O₁ (Stmt.query i :: r, st))).2.log := by
            have hp := log_prefix_run O₁ n (step O₁ (Stmt.query i :: r, st))
            refine hp.subset ?_
            simp [step]
          have hq := hc _ hmem
          simp [step, hq]
      | Stmt.whileNE i body :: r => rfl
      | Stmt.ifNE i a b :: r => rfl
    rw [hstep]
    exact ih _ hc

end CS

import RequestProject.BGS.Classes

/-!
# Encodings

* an enumeration of all programs by natural numbers;
* the format of the strings that are handed to the collapsing oracle `A`:
  `0^j 1 0^m 1 x`, where `j` codes a program together with a polynomial degree,
  `0^m` is padding making the string long, and `x` is the actual input.
-/

namespace CS

deriving instance Countable for Stmt

noncomputable instance : Encodable Stmt := Encodable.ofCountable Stmt

/-- The code of a program. -/
