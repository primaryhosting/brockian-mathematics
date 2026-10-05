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
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem prodAB_eq (a b y m : ℕ) (N : ℕ) (hN : (a + b * y + 1) ^ y < N)
    (hm : b * m ≡ a [MOD N]) :
    prodAB a b y = (b ^ y * (y ! * (m + y).choose y)) % N := by
  have hlt : prodAB a b y < N := lt_of_le_of_lt (prodAB_le a b y) hN
  have h1 : prodAB a b y ≡ ∏ k ∈ range y, (b * m + b * (k + 1)) [MOD N] :=
    modEq_prod y _ _ (fun _ => Nat.ModEq.add_right _ hm.symm)
  have h2 : ∏ k ∈ range y, (b * m + b * (k + 1)) = b ^ y * ∏ k ∈ range y, (m + k + 1) := by
    rw [show (b ^ y : ℕ) = ∏ _k ∈ range y, b by simp, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (by intros; ring)
  have h3 : ∏ k ∈ range y, (m + k + 1) = y ! * (m + y).choose y := by
    have h : ∏ k ∈ range y, (m + k + 1) = (m + 1).ascFactorial y := by
      rw [Nat.ascFactorial_eq_prod_range]
      exact Finset.prod_congr rfl (by intros; ring_nf)
    rw [h, Nat.ascFactorial_eq_factorial_mul_choose]
  rw [h2, h3] at h1
  have h4 := h1.symm
  unfold Nat.ModEq at h4
  rw [h4, Nat.mod_eq_of_lt hlt]

/-- The three-variable version: `prodAB` is a Diophantine function. -/
