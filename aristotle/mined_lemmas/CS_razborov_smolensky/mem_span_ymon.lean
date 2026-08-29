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

lemma mem_span_ymon (z : F) (hz : z ≠ 1) (f : Cube n → F) :
    f ∈ Submodule.span F {g : Cube n → F | ∃ A : Finset (Fin n), g = ymon F z A} := by
  classical
  have hdecomp : f = ∑ x₀ : Cube n, f x₀ • (fun x : Cube n => if x = x₀ then (1 : F) else 0) := by
    funext x
    rw [Finset.sum_apply]
    simp
  rw [hdecomp]
  refine Submodule.sum_mem _ fun x₀ _ => Submodule.smul_mem _ _ ?_
  rw [indicator_eq_gmon]
  have h := gmon_mem_span_gmon (F := F) (fun _ => (1 : F)) (fun _ => z)
    (fun i => fun hc => hz hc.symm) (fun i => if x₀ i then 0 else 1)
    (fun i => if x₀ i then 1 else 0) univ
  refine Submodule.span_le.2 ?_ h
  rintro g ⟨B, -, rfl⟩
  exact Submodule.subset_span ⟨B, rfl⟩

section Finrank

variable (F n)

/-- The number of monomials of degree at most `k`. -/
