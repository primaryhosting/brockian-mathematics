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

theorem natRk_freeOn {α : Type*} (S : Finset α) :
    natRk (Matroid.freeOn (Set.univ : Set α)) (S : Set α) = S.card := by
  unfold natRk
  rw [Matroid.eRk_freeOn (Set.subset_univ _), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid `U_{n,n}` is `(X - 1)^n`. -/
