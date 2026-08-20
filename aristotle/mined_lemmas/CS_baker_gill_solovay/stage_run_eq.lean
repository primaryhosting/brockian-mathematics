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

theorem stage_run_eq (j : ℕ) (hb : Bounded (Mi j) (ki j)) :
    runB (Mi j) oracleB (ones (Nst j), []) (Tst j)
      = runB (Mi j) (Bst j) (ones (Nst j), []) (Tst j) := by
  refine runB_congr (Mi j) (Bst j) oracleB _ _ (fun m hm => ?_)
  set qm := (Mi j).ask (ones (Nst j), []) (ans (Mi j) (Bst j) (ones (Nst j), []) m) with hqm
  have hlen : qm.length ≤ Tst j := by
    have := hb (ones (Nst j), []) (ans (Mi j) (Bst j) (ones (Nst j), []) m)
    simpa [Tst, tb] using this
  by_cases hB : Bst j qm = true
  · rw [hB, oracleB_of_Bst hB]
  · have hBf : Bst j qm = false := by simpa using hB
    rw [hBf]
    cases hO : oracleB qm with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨j', hq, hr⟩ := (oracleB_true_iff' qm).1 hO
        rcases lt_trichotomy j' j with hlt | heq | hgt
        · exact hB (Bst_mono (by omega) (hq ▸ Bst_wit_true hr))
        · apply wit_unqueried j m hm
          rw [← hqm, hq, heq]
        · have h1 : qm.length = Nst j' := by rw [hq]; exact wit_length j'
          have h2 : Nst (j + 1) ≤ Nst j' := Nst_mono (by omega)
          have h3 := Tst_lt_Nst_succ j
          omega

/-! ## The diagonal language -/

/-- The unary language `{1^n : B contains a string of length n}`. -/
