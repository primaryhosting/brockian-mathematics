import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma sum_Icc_id (a b : ℕ) (h : a ≤ b + 1) :
    (∑ i ∈ Finset.Icc a b, i) * 2 + a * (a - 1) = (b + 1) * b := by
  have h1 : (∑ i ∈ Finset.Ico 0 a, i) + (∑ i ∈ Finset.Ico a (b + 1), i)
      = ∑ i ∈ Finset.Ico 0 (b + 1), i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le a) h
  rw [← Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc] at h1
  have h2 := Finset.sum_range_id_mul_two a
  have h3 := Finset.sum_range_id_mul_two (b + 1)
  simp only [Nat.add_sub_cancel] at h3
  generalize a * (a - 1) = X at h2 ⊢
  generalize (b + 1) * b = Y at h3 ⊢
  omega

