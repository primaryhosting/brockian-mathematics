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

theorem tbn_dom (k c : ℕ) : ∃ k', ∀ n : ℕ, tbn k n + c + n + 3 ≤ tbn k' n := by
  refine ⟨k + 1 + (c + 5), fun n => ?_⟩
  simp only [tbn]
  set a := (n + 2) ^ k with ha
  set D := (n + 2) * (c + 5) with hD
  have h1 : (c + 5) < 2 ^ (c + 5) := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ (c + 5) ≤ (n + 2) ^ (c + 5) := Nat.pow_le_pow_left (by omega) _
  have hB : D + 1 ≤ (n + 2) * (n + 2) ^ (c + 5) := by
    have h : (n + 2) * (c + 5) < (n + 2) * (n + 2) ^ (c + 5) := by
      have h' : c + 5 < (n + 2) ^ (c + 5) := lt_of_lt_of_le h1 h2
      gcongr
    omega
  have h3 : (n + 2) ^ (k + 1 + (c + 5)) = a * ((n + 2) * (n + 2) ^ (c + 5)) := by
    rw [ha, ← pow_succ', ← pow_add]; ring_nf
  have h4 : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  have h7 : c + n + 4 ≤ D := by rw [hD]; nlinarith
  rw [h3]
  calc a + c + n + 3 ≤ a + D := by omega
    _ ≤ a * D + a := by nlinarith
    _ = a * (D + 1) := by ring
    _ ≤ a * ((n + 2) * (n + 2) ^ (c + 5)) := Nat.mul_le_mul_left _ hB

/-- Polynomials are eventually dominated by `2^n`; there are arbitrarily large `n`
with `(n+2)^k < 2^n`. -/
