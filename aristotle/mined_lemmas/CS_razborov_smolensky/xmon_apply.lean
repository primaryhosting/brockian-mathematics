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

lemma xmon_apply (A : Finset (Fin n)) (x : Cube n) :
    xmon F A x = if ∀ i ∈ A, x i = true then 1 else 0 := by
  classical
  simp only [xmon, gmon]
  induction A using Finset.induction with
  | empty => simp
  | insert j A hj ih =>
    rw [Finset.prod_insert hj, ih]
    by_cases hall : ∀ i ∈ A, x i = true
    · cases h : x j <;> simp [h, hall]
    · have : ¬ ∀ i ∈ insert j A, x i = true := fun hc => hall fun i hi => hc i (by simp [hi])
      cases h : x j <;> simp [h, hall, this]

