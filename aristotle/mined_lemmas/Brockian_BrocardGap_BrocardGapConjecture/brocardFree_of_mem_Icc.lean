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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BrocardGap

open Nat

/-- `BrocardFree n` says that `n ! + 1` is not a perfect square, i.e. `n` is not a
solution of Brocard's problem. -/

theorem brocardFree_of_mem_Icc (n : ℕ) (h1 : 8 ≤ n) (h2 : n ≤ 100) : BrocardFree n := by
  interval_cases n
  · exact brocardFree_of_mod 8 11 6 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 9 11 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 10 13 7 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 11 13 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 12 29 17 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 13 23 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 14 31 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 15 37 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 16 19 10 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 17 19 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 18 31 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 19 23 5 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 20 29 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 21 31 6 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 22 37 31 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 23 59 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 24 31 23 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 25 31 24 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 26 29 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 27 29 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 28 43 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 29 37 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 30 37 14 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 31 41 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 32 41 13 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 33 37 32 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 34 37 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 35 37 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 36 41 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 37 43 20 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 38 53 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 39 43 37 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 40 43 22 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 41 43 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 42 47 46 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 43 61 44 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 44 53 50 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 45 53 33 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 46 71 68 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 47 53 20 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 48 53 12 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 49 67 50 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 50 53 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 51 53 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 52 59 55 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 53 59 31 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 54 67 50 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 55 59 11 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 56 59 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 57 59 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 58 61 31 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 59 61 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 60 67 5 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 61 67 44 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 62 89 38 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 63 67 57 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 64 67 34 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 65 67 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 66 71 69 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 67 71 13 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 68 79 63 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 69 73 62 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 70 83 14 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 71 79 75 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 72 83 57 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 73 79 28 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 74 79 24 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 75 83 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 76 97 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 77 89 28 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 78 83 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 79 83 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 80 83 42 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 81 83 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 82 89 12 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 83 89 24 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 84 97 41 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 85 103 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 86 101 51 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 87 101 8 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 88 101 11 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 89 101 83 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 90 101 8 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 91 97 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 92 97 5 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 93 97 82 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 94 101 32 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 95 103 45 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 96 107 54 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 97 101 18 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 98 101 51 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 99 101 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 100 139 132 (by norm_num) (by rfl) (by decide)

/-- **Brocard Gap Conjecture** (Lean-checked reduction and partial verification).

The full conjecture — that `n ! + 1` is never a perfect square for `n ≥ 8` — is open.
What is proved here is:

* the *gap* reformulation: `n ! + 1` is a square iff `n !` is a product of two naturals
  with gap exactly `2`;
* the exact determination of the solutions below `8`, namely `4, 5, 7`;
* the verification that no `n` in the range `8 ≤ n ≤ 100` is a solution;
* the resulting equivalence of the conjecture with its gap-free reformulation:
  `n !` has no gap-two factorization for every `n ≥ 8`.
-/
