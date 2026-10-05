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
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The set of coprime residues mod `9` in `range 9`. -/
lemma coprime_filter_nine :
    ((Finset.range 9).filter fun i => Nat.Coprime 9 i) = ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
  decide

/-- The sum of the primitive `9`-th roots of unity, written as a sum of powers of a fixed
primitive root, vanishes. -/
lemma sum_pow_primitive_nine {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9) :
    ∑ i ∈ (Finset.range 9).filter (fun i => Nat.Coprime 9 i), ζ ^ i = 0 := by
  have h9 : ζ ^ 9 = 1 := hζ.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (ζ ^ 3 - 1) * (ζ ^ 6 + ζ ^ 3 + 1) = 0 := by linear_combination h9
  have hsum : ζ ^ 6 + ζ ^ 3 + 1 = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h3
    · exact h
  rw [coprime_filter_nine]
  norm_num [Finset.sum_insert, Finset.mem_insert]
  linear_combination (ζ + ζ ^ 2) * hsum

/-- The sum of the primitive `9`-th roots of unity in `ℂ` equals `μ 9`. -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 9 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 9), Complex.isPrimitiveRoot_exp 9 (by norm_num)⟩
  have hbij : ∑ i ∈ (Finset.range 9).filter (fun i => Nat.Coprime 9 i), ζ ^ i
      = ∑ z ∈ primitiveRoots 9 ℂ, z := by
    refine Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      exact (mem_primitiveRoots (by norm_num)).2 (hζ.pow_of_coprime a ha.2.symm)
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_range] at ha hb
      exact hζ.pow_inj ha.1 hb.1 hab
    · intro ξ hξ
      rw [mem_primitiveRoots (by norm_num), hζ.isPrimitiveRoot_iff] at hξ
      obtain ⟨i, hin, hi, H⟩ := hξ
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hin, hi.symm⟩, H⟩
    · intro a _
      rfl
  have hsq : ¬ Squarefree 9 := by
    intro h
    have h3 := h 3 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at h3
    exact absurd h3 (by norm_num)
  have hmu : ArithmeticFunction.moebius 9 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
  rw [← hbij, sum_pow_primitive_nine hζ, hmu]
  norm_num

end Math

