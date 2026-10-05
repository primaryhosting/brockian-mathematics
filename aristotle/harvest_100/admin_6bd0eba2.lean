/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction

open scoped ArithmeticFunction.Moebius

namespace Math

/-- If `ζ` is a primitive `8`-th root of unity in `ℂ`, then `ζ ^ 4 = -1`. -/
lemma pow_four_eq_neg_one_of_isPrimitiveRoot_eight {ζ : ℂ} (h : IsPrimitiveRoot ζ 8) :
    ζ ^ 4 = -1 := by
  have h8 : ζ ^ 8 = 1 := h.pow_eq_one
  have hfac : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exfalso
    have h4 : ζ ^ 4 = 1 := by linear_combination h1
    exact h.pow_ne_one_of_pos_of_lt (l := 4) (by norm_num) (by norm_num) h4
  · linear_combination h2

/-- The negation of a primitive `8`-th root of unity is again a primitive `8`-th root
of unity. -/
lemma isPrimitiveRoot_neg_of_isPrimitiveRoot_eight {ζ : ℂ} (h : IsPrimitiveRoot ζ 8) :
    IsPrimitiveRoot (-ζ) 8 := by
  have h4 : ζ ^ 4 = -1 := pow_four_eq_neg_one_of_isPrimitiveRoot_eight h
  have hneg : -ζ = ζ ^ 5 := by
    have h5 : ζ ^ 5 = ζ ^ 4 * ζ := by ring
    rw [h5, h4]; ring
  rw [hneg]
  exact h.pow_of_coprime 5 (by decide)

/-- `μ 8 = 0`, since `8` is not squarefree. -/
lemma moebius_eight : μ 8 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  have h2 := hs 2 ⟨2, by norm_num⟩
  norm_num at h2

/-- **The sum of the primitive 8-th roots of unity equals `μ(8)`.** -/
theorem mobius_root_sum_8 :
    ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = ((μ 8 : ℤ) : ℂ) := by
  rw [moebius_eight]
  push_cast
  refine Finset.sum_involution (fun a _ => -a) ?_ ?_ ?_ ?_
  · intro a _
    ring
  · intro a _ ha0 hcon
    apply ha0
    have h2 : (2 : ℂ) * a = 0 := by linear_combination -hcon
    simpa using h2
  · intro a ha
    rw [mem_primitiveRoots (by norm_num)] at ha ⊢
    exact isPrimitiveRoot_neg_of_isPrimitiveRoot_eight ha
  · intro a _
    ring

end Math

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

