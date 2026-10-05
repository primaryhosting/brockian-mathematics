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

lemma indicator_eq_gmon (x₀ : Cube n) :
    (fun x : Cube n => if x = x₀ then (1 : F) else 0)
      = gmon F (fun i => if x₀ i then 0 else 1) (fun i => if x₀ i then 1 else 0) univ := by
  funext x
  simp only [gmon]
  rw [show (∏ i : Fin n, (if x i then (if x₀ i then (1 : F) else 0)
      else (if x₀ i then 0 else 1)))
      = ∏ i : Fin n, (if x i = x₀ i then (1 : F) else 0) from
    Finset.prod_congr rfl fun i _ => by cases h : x i <;> cases h₀ : x₀ i <;> simp [h, h₀]]
  rw [Finset.prod_boole]
  by_cases h : x = x₀
  · subst h; simp
  · have hnot : ¬ ∀ i ∈ univ, x i = x₀ i := fun hc => h (funext fun i => hc i (mem_univ i))
    rw [if_neg h, if_neg hnot]

/-- Every function on the cube is a combination of the `ymon`'s. -/
