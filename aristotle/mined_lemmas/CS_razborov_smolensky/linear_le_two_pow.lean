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

import Mathlib
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma linear_le_two_pow (C i : ℕ) (hi : C ^ 2 + C ≤ i) : C * (i + 1) ≤ 2 ^ i := by
  have hCi : C ≤ i := le_trans (Nat.le_add_left C (C ^ 2)) hi
  have h1 : 2 ^ i = 2 ^ C * 2 ^ (i - C) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : (C + 1) * (i - C + 1) ≤ 2 ^ C * 2 ^ (i - C) :=
    Nat.mul_le_mul (succ_le_two_pow C) (succ_le_two_pow (i - C))
  have h3 : C * (i + 1) ≤ (C + 1) * (i - C + 1) := by
    have : i - C + C = i := by omega
    nlinarith [this, hi, sq_nonneg C]
  omega

/-- A polynomial is eventually dominated by `2 ^ j`. -/
