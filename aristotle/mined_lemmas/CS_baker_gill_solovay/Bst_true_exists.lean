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

theorem Bst_true_exists : ∀ (j : ℕ) (q : Str), Bst j q = true →
    ∃ j' < j, q = wit j' ∧ stageRun j' = false := by
  intro j
  induction j with
  | zero => intro q h; rw [Bst_zero] at h; exact absurd h (by simp)
  | succ j ih =>
      intro q h
      rw [Bst_succ] at h
      by_cases hs : stageRun j = true
      · rw [if_pos hs] at h
        obtain ⟨j', hj', hq, hr⟩ := ih q h
        exact ⟨j', by omega, hq, hr⟩
      · rw [if_neg hs] at h
        by_cases hb : Bst j q = true
        · obtain ⟨j', hj', hq, hr⟩ := ih q hb
          exact ⟨j', by omega, hq, hr⟩
        · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
          rcases h with h | h
          · exact absurd h hb
          · exact ⟨j, by omega, h, by simpa using hs⟩

/-! ## The oracle `B` -/

open scoped Classical in
/-- The oracle `B` of the second half of the Baker–Gill–Solovay theorem. -/
