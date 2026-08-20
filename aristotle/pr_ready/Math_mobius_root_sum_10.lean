/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Statement: The sum of the primitive 10-th roots of unity equals μ(10).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Finset

namespace Math

/-- The Möbius function at `10` equals `1`. -/
lemma moebius_ten : (ArithmeticFunction.moebius 10 : ℤ) = 1 := by
  have h : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- The index set of exponents giving primitive `10`-th roots of unity. -/
lemma coprime_filter_ten : (range 10).filter (Nat.Coprime 10) = {1, 3, 7, 9} := by decide

/-- A primitive `10`-th root of unity `ζ` in a domain satisfies `ζ^5 = -1`. -/
lemma pow_five_eq_neg_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) : ζ ^ 5 = -1 := by
  have h10 : (ζ ^ 5) ^ 2 = 1 := by
    rw [← pow_mul]; exact_mod_cast h.pow_eq_one
  have h5 : ζ ^ 5 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  rcases (mul_self_eq_one_iff (a := ζ ^ 5)).mp (by linear_combination h10) with h1 | h1
  · exact absurd h1 h5
  · exact h1

/-- The algebraic relation satisfied by a primitive `10`-th root of unity. -/
lemma cyclotomic_ten_eq_zero {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hz
    have hζ : ζ = -1 := by linear_combination hz
    have h2 : ζ ^ 2 = 1 := by rw [hζ]; norm_num
    exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h2
  have hprod : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.mp hprod with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- The sum of the four primitive `10`-th roots of unity, expressed via a fixed primitive root. -/
lemma sum_pow_eq_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 + ζ ^ 3 + ζ ^ 7 + ζ ^ 9 = 1 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hc := cyclotomic_ten_eq_zero h
  have h7 : ζ ^ 7 = -ζ ^ 2 := by
    have : ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
    rw [this, h5]; ring
  have h9 : ζ ^ 9 = -ζ ^ 4 := by
    have : ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := by ring
    rw [this, h5]; ring
  rw [h7, h9]
  linear_combination -hc

/-- The sum of the primitive `10`-th roots of unity in `ℂ` equals `μ(10)`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = ((ArithmeticFunction.moebius 10 : ℤ) : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 10)) 10 :=
    Complex.isPrimitiveRoot_exp 10 (by norm_num)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / 10)
  have key : ∑ i ∈ (range 10).filter (Nat.Coprime 10), ζ ^ i
      = ∑ z ∈ primitiveRoots 10 ℂ, z := by
    refine Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_range] at ha
      exact (mem_primitiveRoots (by norm_num)).mpr (h.pow_of_coprime a ha.2.symm)
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      exact h.pow_inj ha.1 hb.1 hab
    · intro ξ hξ
      rw [mem_primitiveRoots (by norm_num), h.isPrimitiveRoot_iff] at hξ
      obtain ⟨i, hin, hi, H⟩ := hξ
      exact ⟨i, by simp only [mem_filter, mem_range]; exact ⟨hin, hi.symm⟩, H⟩
    · intro a _; rfl
  rw [← key, coprime_filter_ten, moebius_ten]
  norm_num
  linear_combination sum_pow_eq_one h

end Math


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

