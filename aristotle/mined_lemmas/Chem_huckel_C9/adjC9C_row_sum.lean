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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ## The adjacency matrix of the cycle graph `C₉` -/

/-- The adjacency matrix of the cycle graph `C₉`, i.e. the Hückel matrix of the
cyclononatetraenyl π-system with `α = 0` and `β = 1`. -/

lemma adjC9C_row_sum (i : Fin 9) (z : ℂ) :
    ∑ j : Fin 9, adjC9C i j * z ^ (j : ℕ)
      = z ^ ((i + 1 : Fin 9) : ℕ) + z ^ ((i - 1 : Fin 9) : ℕ) := by
  have hne : (i + 1 : Fin 9) ≠ i - 1 := succ_ne_pred i
  have key : ∀ j : Fin 9, adjC9C i j * z ^ (j : ℕ)
      = (if j = i + 1 then z ^ ((i + 1 : Fin 9) : ℕ) else 0)
        + (if j = i - 1 then z ^ ((i - 1 : Fin 9) : ℕ) else 0) := by
    intro j
    rw [adjC9C_apply]
    by_cases h1 : j = i + 1
    · subst h1; simp [hne]
    · by_cases h2 : j = i - 1
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1 : Fin 9) (fun _ => z ^ ((i + 1 : Fin 9) : ℕ)),
    Finset.sum_ite_eq' Finset.univ (i - 1 : Fin 9) (fun _ => z ^ ((i - 1 : Fin 9) : ℕ))]
  simp

