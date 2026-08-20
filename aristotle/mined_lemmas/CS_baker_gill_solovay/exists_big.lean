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

theorem exists_big (k m : ℕ) : ∃ n, m < n ∧ tbn k n < 2 ^ n := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (one_lt_two)
  have hc : (0 : ℝ) < ((2 : ℝ) * 3 ^ k)⁻¹ := by positivity
  have h2 := h.def hc
  rw [Filter.eventually_atTop] at h2
  obtain ⟨N, hN⟩ := h2
  refine ⟨max (max N m.succ) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans (le_max_right N m.succ) (le_max_left _ _))
  · simp only [tbn]
    set n := max (max N m.succ) 1 with hn
    have hn1 : 1 ≤ n := le_max_right _ _
    have hnN : N ≤ n := le_trans (le_max_left N m.succ) (le_max_left _ _)
    have key := hN n hnN
    simp only [norm_pow, Real.norm_natCast, Real.norm_ofNat] at key
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h3 : ((n : ℝ) + 2) ^ k ≤ 3 ^ k * (n : ℝ) ^ k := by
      rw [← mul_pow]
      gcongr
      linarith
    have h4 : (3 : ℝ) ^ k * (n : ℝ) ^ k ≤ 3 ^ k * (((2 : ℝ) * 3 ^ k)⁻¹ * 2 ^ n) := by
      have h0 : (0 : ℝ) < 3 ^ k := by positivity
      exact mul_le_mul_of_nonneg_left key (le_of_lt h0)
    have h5 : (3 : ℝ) ^ k * (((2 : ℝ) * 3 ^ k)⁻¹ * 2 ^ n) = 2 ^ n / 2 := by field_simp
    have h6 : ((n : ℝ) + 2) ^ k < 2 ^ n := by
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      calc ((n : ℝ) + 2) ^ k ≤ 3 ^ k * (n : ℝ) ^ k := h3
        _ ≤ 2 ^ n / 2 := by rw [← h5]; exact h4
        _ < 2 ^ n := by linarith
    have hcast : (((n + 2) ^ k : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; exact h6
    exact_mod_cast hcast

end CS

/-
# A relativized model of computation

This file sets up the model of oracle computation used in the formalization of the
Baker–Gill–Solovay theorem.

An *oracle machine* is a pair of computable functions: `ask` produces the next query
from the input and the list of oracle answers received so far, and `out` produces the
final verdict from the input and the list of answers.  A machine is run for a number of
steps given by a polynomial bound in the length of the input, and its queries are
required to be of length at most that same bound.

The resources that are polynomially bounded are therefore the number of oracle queries
and the length of each query, while the transitions between queries are required to be
computable.  Since there are only countably many machines, the diagonalization argument
for the second oracle goes through, and the class `P^A` contains, for instance, every
computable language (via a machine that ignores its oracle).
-/
import Mathlib

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented as its characteristic function. -/
abbrev Oracle := Str → Bool

/-- A language is a set of strings. -/
abbrev Language := Set Str

/-- An oracle machine: `ask z l` is the next query on input `z` after receiving the
answers `l`, and `out z l` is the verdict. The input `z` is a pair (proper input,
certificate); machines used for deterministic computation simply ignore the second
component. Both functions are required to be computable, so that there are only
countably many machines. -/
structure OM where
  ask : Str × Str → List Bool → Str
  out : Str × Str → List Bool → Bool
  ask_computable : Computable₂ ask
  out_computable : Computable₂ out

/-- The list of the first `n` oracle answers in the run of `M` with oracle `O` on `z`. -/
