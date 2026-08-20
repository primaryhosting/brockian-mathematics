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

import RequestProject.BGS.PartA
import RequestProject.BGS.PartB

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header block above is placed after the `import` lines because Lean 4 requires
`import` commands to come first in a file.)

The model of relativized computation is developed in `RequestProject.BGS.Model`:

* an *oracle* is a set of binary strings, `Oracle := Str → Bool`;
* an *oracle machine* `OM` is a pair of computable functions `ask`, `out`: `ask z l`
  returns the next query on input `z` (a pair of an input and a certificate) given the
  list `l` of oracle answers received so far, and `out z l` returns the verdict;
* `Bounded M k` says that all queries of `M` have length at most `(|x|+2)^k`, where `x`
  is the proper input, and a machine is run for `(|x|+2)^k` steps;
* `Po A L` (`L ∈ P^A`) and `NPo A L` (`L ∈ NP^A`) are the usual definitions, and
  `PClass A`, `NPClass A` are the corresponding classes of languages.

`RequestProject.BGS.PartA` builds an oracle `A` (by recursion on the length of strings)
which encodes acceptance of the `NP^A` computations, so that `P^A = NP^A`.

`RequestProject.BGS.PartB` builds an oracle `B` by diagonalization, so that the unary
language `LB = {1^n : B contains a string of length n}` lies in `NP^B` but not in `P^B`.
-/

namespace CS

/-- **Baker–Gill–Solovay theorem** (the relativization barrier): there is an oracle `A`
with `P^A = NP^A` and an oracle `B` with `P^B ≠ NP^B`. -/

theorem LB_not_in_Po : ¬ Po oracleB LB := by
  rintro ⟨M, k, hb, hL⟩
  obtain ⟨i, rfl⟩ := mach_surjective M
  set j := Nat.pair i k with hj
  have hMi : Mi j = mach i := Mi_pair i k
  have hki : ki j = k := ki_pair i k
  have hbj : Bounded (Mi j) (ki j) := by rw [hMi, hki]; exact hb
  set n := Nst j with hn
  have htb : tb k (ones n) = Tst j := by
    simp [tb, Tst, hki, tbn, hn]
  have hrun : runB (mach i) oracleB (ones n, []) (tb k (ones n)) = stageRun j := by
    rw [htb, ← hMi]
    exact stage_run_eq j hbj
  have hiff := hL (ones n)
  rw [hrun] at hiff
  by_cases hs : stageRun j = true
  · have hmem : ones n ∈ LB := hiff.2 hs
    obtain ⟨-, w, hw, hwB⟩ := hmem
    obtain ⟨j', hq, hr⟩ := (oracleB_true_iff' w).1 hwB
    have hlen : Nst j' = n := by rw [← wit_length j', ← hq, hw]; simp
    have : j' = j := Nst_inj (by rw [hlen, hn])
    subst this
    rw [hr] at hs
    exact absurd hs (by simp)
  · have hsf : stageRun j = false := by simpa using hs
    have hmem : ones n ∈ LB := by
      refine ⟨by simp, wit j, ?_, ?_⟩
      · rw [wit_length j]; simp [hn]
      · exact oracleB_of_Bst (Bst_wit_true hsf)
    have := hiff.1 hmem
    rw [hsf] at this
    exact absurd this (by simp)

/-- **Second half of Baker–Gill–Solovay**: there is an oracle `B` with `P^B ≠ NP^B`. -/
