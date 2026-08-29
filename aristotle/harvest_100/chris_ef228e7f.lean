import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
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

set_option grind.warning false

namespace Math

/-- A primitive 12-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 6 = -1`. -/
lemma pow_six_eq_neg_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 12) : ζ ^ 6 = -1 := by
  have h12 : (ζ ^ 6) ^ 2 = 1 := by
    rw [← pow_mul]; exact hζ.pow_eq_one
  have hne : ζ ^ 6 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 6) (by norm_num) (by norm_num)
  have h12' : (ζ ^ 6) * (ζ ^ 6) = 1 := by rw [← sq]; exact h12
  rcases mul_self_eq_one_iff.mp h12' with h | h
  · exact absurd h hne
  · exact h

/-- The finset of primitive 12-th roots of unity in `ℂ`, described explicitly in terms of
one of them. -/
lemma primitiveRoots_twelve_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 12) :
    primitiveRoots 12 ℂ = {ζ ^ 1, ζ ^ 5, ζ ^ 7, ζ ^ 11} := by
  have hinj : ∀ i j : ℕ, i < 12 → j < 12 → ζ ^ i = ζ ^ j → i = j := by
    intro i j hi hj h
    exact hζ.pow_inj hi hj h
  have hsub : ({ζ ^ 1, ζ ^ 5, ζ ^ 7, ζ ^ 11} : Finset ℂ) ⊆ primitiveRoots 12 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact hζ.pow_of_coprime 1 (by norm_num)
    · exact hζ.pow_of_coprime 5 (by decide)
    · exact hζ.pow_of_coprime 7 (by decide)
    · exact hζ.pow_of_coprime 11 (by decide)
  have hcard : (primitiveRoots 12 ℂ).card = 4 := by
    rw [hζ.card_primitiveRoots]; decide
  have hcard2 : ({ζ ^ 1, ζ ^ 5, ζ ^ 7, ζ ^ 11} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      intro h; exact absurd (hinj 7 11 (by norm_num) (by norm_num) h) (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact absurd (hinj 5 7 (by norm_num) (by norm_num) h) (by norm_num)
      · exact absurd (hinj 5 11 (by norm_num) (by norm_num) h) (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact absurd (hinj 1 5 (by norm_num) (by norm_num) h) (by norm_num)
      · exact absurd (hinj 1 7 (by norm_num) (by norm_num) h) (by norm_num)
      · exact absurd (hinj 1 11 (by norm_num) (by norm_num) h) (by norm_num)
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])).symm

/-- The sum of the primitive 12-th roots of unity in `ℂ` equals `μ(12) = 0`. -/
theorem mobius_root_sum_12 :
    ∑ ζ ∈ primitiveRoots 12 ℂ, ζ = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12)) 12 :=
    Complex.isPrimitiveRoot_exp 12 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12) with hζdef
  have h6 : ζ ^ 6 = -1 := pow_six_eq_neg_one hζ
  have hmu : (ArithmeticFunction.moebius 12 : ℂ) = 0 := by
    have : ArithmeticFunction.moebius 12 = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
    rw [this]; norm_num
  rw [primitiveRoots_twelve_eq hζ, hmu]
  have hinj : ∀ i j : ℕ, i < 12 → j < 12 → ζ ^ i = ζ ^ j → i = j := fun i j hi hj h =>
    hζ.pow_inj hi hj h
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · have h7 : ζ ^ 7 = -ζ ^ 1 := by
      have : ζ ^ 7 = ζ ^ 6 * ζ ^ 1 := by ring
      rw [this, h6]; ring
    have h11 : ζ ^ 11 = -ζ ^ 5 := by
      have : ζ ^ 11 = ζ ^ 6 * ζ ^ 5 := by ring
      rw [this, h6]; ring
    rw [h7, h11]; ring
  · simp only [Finset.mem_singleton]
    intro h; exact absurd (hinj 7 11 (by norm_num) (by norm_num) h) (by norm_num)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact absurd (hinj 5 7 (by norm_num) (by norm_num) h) (by norm_num)
    · exact absurd (hinj 5 11 (by norm_num) (by norm_num) h) (by norm_num)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact absurd (hinj 1 5 (by norm_num) (by norm_num) h) (by norm_num)
    · exact absurd (hinj 1 7 (by norm_num) (by norm_num) h) (by norm_num)
    · exact absurd (hinj 1 11 (by norm_num) (by norm_num) h) (by norm_num)

end Math

