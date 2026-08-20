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

theorem LB_in_NPo : NPo oracleB LB := by
  refine ⟨verifier, 1, ?_, fun x => ?_⟩
  · intro z l
    have : tb 1 z.1 = z.1.length + 2 := by simp [tb, tbn]
    rw [this]
    by_cases h : z.2.length ≤ z.1.length
    · simp only [verifier, h, if_pos]
      omega
    · simp only [verifier, h, if_false]
      simp
  · have hT : 1 ≤ tb 1 x := tb_pos 1 x
    constructor
    · rintro ⟨hx, w, hw, hwB⟩
      refine ⟨w, ?_, ?_⟩
      · rw [hw]; simp [tb, tbn]
      · rw [runB_verifier oracleB x w _ hT, if_pos (by omega : w.length ≤ x.length), hwB]
        rw [if_pos (by rw [hw]; exact hx)]
    · rintro ⟨y, -, hy⟩
      rw [runB_verifier oracleB x y _ hT] at hy
      by_cases hx : x = ones y.length
      · rw [if_pos hx] at hy
        have hlen : y.length = x.length := by rw [hx]; simp
        rw [if_pos (by omega : y.length ≤ x.length)] at hy
        exact ⟨by rw [hx]; simp, y, hlen, hy⟩
      · rw [if_neg hx] at hy
        exact absurd hy (by simp)

