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
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem apProd_modEq (a b c m M : ℕ) (h : b * c ≡ a [MOD M]) :
    apProd a b m ≡ b ^ m * (m.factorial * (c + m).choose m) [MOD M] := by
  have hasc : ∏ i ∈ Finset.Icc 1 m, (c + i) = (c+1).ascFactorial m := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]; ring
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
  push_cast [apProd] at h ⊢
  have hcongr : ∀ i ∈ Finset.Icc 1 m, ((a : ZMod M) + i * b) = b * (c + i) := by
    intro i _
    rw [← h]; ring
  rw [Finset.prod_congr rfl hcongr, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
  have hasc' : ∏ i ∈ Finset.Icc 1 m, ((c : ZMod M) + i)
      = (((c+1).ascFactorial m : ℕ) : ZMod M) := by
    rw [← hasc]; push_cast; ring
  rw [hasc', Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  ring_nf

/-- Characterisation of the product of an arithmetic progression by congruences: this is what
makes it Diophantine. -/
