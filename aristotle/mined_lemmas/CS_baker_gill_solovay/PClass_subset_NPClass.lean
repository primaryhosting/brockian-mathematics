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

theorem PClass_subset_NPClass (O : Oracle) : PClass O ⊆ NPClass O := by
  rintro L ⟨M, k, hhalt, hacc⟩
  refine ⟨clearWitness M, k + 1, ?_, ?_⟩
  · intro x w
    have hbig : pb k x.length + 2 ≤ pb (k + 1) (x.length + w.length) := by
      have h1 : pb (k + 1) x.length ≤ pb (k + 1) (x.length + w.length) :=
        pb_mono_right (by omega)
      have h2 : pb k x.length + pb k x.length ≤ pb (k + 1) x.length := by
        unfold pb
        have : (x.length + 2) ^ (k + 1) * 2 ≤ (x.length + 2) ^ (k + 1) * (x.length + 2) := by
          exact Nat.mul_le_mul_left _ (by omega)
        calc (x.length + 2) ^ (k + 1) + (x.length + 2) ^ (k + 1)
            = (x.length + 2) ^ (k + 1) * 2 := by ring
          _ ≤ (x.length + 2) ^ (k + 1) * (x.length + 2) := this
          _ = (x.length + 2) ^ (k + 1 + 1) := by ring
      have h3 := two_le_pb k x.length
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hbig
    unfold Halts
    rw [show pb (k + 1) (x.length + w.length) = (pb k x.length + d) + 2 by omega,
      run_clearWitness]
    have := (hhalt x).mono (t' := pb k x.length + d) (by omega)
    exact this
  · intro x
    rw [hacc x]
    constructor
    · intro hA
      refine ⟨[], by simp, ?_⟩
      have hbig : pb k x.length + 2 ≤ pb (k + 1) (x.length + ([] : Str).length) := by
        have h1 : pb k x.length + pb k x.length ≤ pb (k + 1) x.length := by
          unfold pb
          calc (x.length + 2) ^ (k + 1) + (x.length + 2) ^ (k + 1)
              = (x.length + 2) ^ (k + 1) * 2 := by ring
            _ ≤ (x.length + 2) ^ (k + 1) * (x.length + 2) :=
                Nat.mul_le_mul_left _ (by omega)
            _ = (x.length + 2) ^ (k + 1 + 1) := by ring
        have h3 := two_le_pb k x.length
        simp only [List.length_nil, Nat.add_zero]
        omega
      unfold Acc
      rw [show pb (k + 1) (x.length + ([] : Str).length)
            = (pb (k + 1) (x.length + ([] : Str).length) - 2) + 2 by omega,
        run_clearWitness]
      have hle : pb k x.length ≤ pb (k + 1) (x.length + ([] : Str).length) - 2 := by omega
      exact hA.mono hle
    · rintro ⟨w, -, hA⟩
      have h2 : 2 ≤ pb (k + 1) (x.length + w.length) := two_le_pb _ _
      set t := pb (k + 1) (x.length + w.length) - 2 with ht
      have hA' : Acc M O x [] t := by
        unfold Acc at hA ⊢
        rwa [show pb (k + 1) (x.length + w.length) = t + 2 by omega, run_clearWitness] at hA
      by_cases hle : pb k x.length ≤ t
      · exact (Acc_iff_of_halts (hhalt x) hle).mp hA'
      · exact hA'.mono (by omega)

end CS

import RequestProject.BGS.CheckProg

/-!
# The separating oracle `B`

`B` is built by stages.  Stage `i` diagonalizes against the `i`-th pair (program, degree):
a fresh length `n` is chosen, so large that the time bound `pb k n` is smaller than the
number `2 ^ n` of strings of length `n`.  If the machine accepts `1^n` with the oracle
built so far, no string of length `n` is ever added; otherwise a string of length `n`
that the machine did not query is added.  In both cases the machine disagrees with
`Lang B` on the input `1^n`.
-/

namespace CS

/-! ### Two auxiliary existence statements -/

/-- Polynomials are eventually dominated by `2 ^ n`. -/
