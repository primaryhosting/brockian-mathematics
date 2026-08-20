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

/-!
# Log-concavity of the characteristic polynomial of a matroid (base case)

The Adiprasito–Huh–Katz theorem states that the coefficients `w₀, w₁, …, w_r` of the
characteristic polynomial of a matroid form a log-concave sequence in absolute value,
i.e. `|w_{k+1}|² ≥ |w_k| · |w_{k+2}|`.

Here we formalise the Whitney rank-generating definition of the characteristic polynomial
of a matroid on a finite ground type, and prove the base case of the theorem: the free
(Boolean) matroid `U_{n,n}` on an `n`-element ground set, whose characteristic polynomial
is `(X - 1)^n`, so that the absolute values of its coefficients are the binomial
coefficients `C(n, k)`, which are log-concave.
-/

namespace Frontier

open Polynomial Finset Matroid

/-- The `ℕ`-valued rank function of a matroid. -/

theorem charPoly_eq_zero_of_isLoop {α : Type*} [Fintype α] (M : Matroid α) {e : α}
    (he : M.IsLoop e) : charPoly M = 0 := by
  unfold charPoly
  refine Finset.sum_involution (fun S _ => if e ∈ S then S.erase e else insert e S)
    (fun S _ => ?_) (fun S _ _ => ?_) (fun S _ => Finset.mem_univ _) (fun S _ => ?_)
  · by_cases hS : e ∈ S
    · simp only [hS, if_true]
      have hcoe : ((S : Set α)) = insert e ((S.erase e : Finset α) : Set α) := by
        rw [← Finset.coe_insert, Finset.insert_erase hS]
      have hrk : natRk M (S : Set α) = natRk M ((S.erase e : Finset α) : Set α) := by
        rw [hcoe]; exact natRk_insert_of_isLoop M he _
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, hS⟩
      have hcard : S.card = (S.erase e).card + 1 := by
        rw [Finset.card_erase_of_mem hS]; omega
      rw [hrk, hcard, pow_succ]
      ring
    · simp only [hS, if_false]
      have hrk : natRk M ((insert e S : Finset α) : Set α) = natRk M (S : Set α) := by
        rw [Finset.coe_insert]; exact natRk_insert_of_isLoop M he _
      have hcard : (insert e S).card = S.card + 1 := Finset.card_insert_of_notMem hS
      rw [hrk, hcard, pow_succ]
      ring
  · by_cases hS : e ∈ S
    · simp only [hS, if_true]
      intro h
      exact Finset.notMem_erase e S (by rw [h]; exact hS)
    · simp only [hS, if_false]
      intro h
      exact hS (h ▸ Finset.mem_insert_self e S)
  · by_cases hS : e ∈ S
    · simp [hS, Finset.insert_erase hS]
    · simp [hS, Finset.erase_insert hS]

/-- A matroid with a loop trivially has log-concave characteristic polynomial coefficients,
since they all vanish. -/
