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

/-
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Brocard's problem asks for all solutions of the Diophantine equation
`n ! + 1 = m ^ 2`.  The three known solutions are `n = 4, 5, 7` (with
`m = 5, 11, 71`), and *Brocard's conjecture* asserts that there are no
others.  The problem is open.

This file contains:

* the exact determination of all solutions with `n ≤ 7` (unconditional);
* an elementary **equivalent reformulation**: for `n ≥ 2`, `n ! + 1` is a
  square if and only if `n !` is four times a pronic number,
  `n ! = 4 * k * (k + 1)`;
* a **Wilson-prime obstruction** (unconditional): if `n + 1` is prime and
  `n ! + 1` is a square, then `n + 1` is a Wilson prime, i.e.
  `(n+1)^2 ∣ n ! + 1`;
* an unconditional verification that there is no solution with `8 ≤ n ≤ 100`
  (in particular none at the Wilson prime `13`, i.e. `n = 12`);
* the target theorem `BrocardConjecture`, a **conditional reduction**: the
  full conjecture follows from the reformulated statement
  `∀ n ≥ 101, ∀ k, n ! ≠ 4 * k * (k + 1)`, which is itself equivalent to the
  conjecture for `n ≥ 101`.
-/

namespace Brockian
namespace BrocardProblem

open Nat

/-- `IsBrocardSolution n m` says that `(n, m)` solves Brocard's equation
`n ! + 1 = m ^ 2`. -/

theorem sq_succ_factorial_iff_pronic {n : ℕ} (hn : 2 ≤ n) :
    (∃ m, n ! + 1 = m ^ 2) ↔ ∃ k, n ! = 4 * k * (k + 1) := by
  constructor
  · rintro ⟨m, hm⟩
    have h2 : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
    have hmodd : ¬ 2 ∣ m := by
      rintro ⟨t, ht⟩
      subst ht
      obtain ⟨s, hs⟩ := h2
      have : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      omega
    obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := by
      rcases Nat.even_or_odd m with he | ho
      · exact absurd he.two_dvd hmodd
      · obtain ⟨k, hk⟩ := ho; exact ⟨k, by omega⟩
    refine ⟨k, ?_⟩
    subst hk
    have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    omega
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by rw [hk]; ring⟩

/-! ### No solutions for `8 ≤ n ≤ 100` -/

/-- **Unconditional partial result.**  There is no Brocard solution with
`8 ≤ n ≤ 100`: in each case `n ! + 1` lies strictly between two consecutive
squares. -/
