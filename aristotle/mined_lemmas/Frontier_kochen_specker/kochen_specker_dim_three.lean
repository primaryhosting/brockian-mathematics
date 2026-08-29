import Mathlib

/-!
# The rays of a three dimensional Kochen–Specker configuration

The 33 rays of a Kochen–Specker configuration in `ℝ³` (coordinates in `{0, ±1, ±√2}`),
together with the auxiliary vectors completing each orthogonal pair to a frame, and the
boolean bookkeeping lemmas used in the case analysis.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Frontier
namespace KS3

/-- The three dimensional real Hilbert space. -/
abbrev V3 := EuclideanSpace ℝ (Fin 3)


theorem kochen_specker_dim_three :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 3) → Bool,
        ∀ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if f (v i) then (1 : ℕ) else 0) = 1 := by
  rintro ⟨f, hf⟩
  have H3 : ∀ a b c : KS3.V3, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      inner ℝ a b = (0 : ℝ) → inner ℝ a c = (0 : ℝ) → inner ℝ b c = (0 : ℝ) →
      (if f a then 1 else 0) + (if f b then 1 else 0) + (if f c then 1 else 0) = (1 : ℕ) := by
    intro a b c ha hb hc hab hac hbc
    have hba : inner ℝ b a = (0 : ℝ) := by rw [real_inner_comm]; exact hab
    have hca : inner ℝ c a = (0 : ℝ) := by rw [real_inner_comm]; exact hac
    have hcb : inner ℝ c b = (0 : ℝ) := by rw [real_inner_comm]; exact hbc
    have key := hf ![a, b, c]
      (by intro i; fin_cases i <;> simpa using ‹_›)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    rw [Fin.sum_univ_three] at key
    simpa using key
  have E0 : (if f KS3.r0 then 1 else 0) + (if f KS3.r1 then 1 else 0)
      + (if f KS3.r8 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r0 KS3.r1 KS3.r8 KS3.r0_ne KS3.r1_ne KS3.r8_ne
    (by
      simp only [KS3.r0, KS3.r1, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r0, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r1, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E1 : (if f KS3.r0 then 1 else 0) + (if f KS3.r23 then 1 else 0)
      + (if f KS3.r40 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r0 KS3.r23 KS3.r40 KS3.r0_ne KS3.r23_ne KS3.r40_ne
    (by
      simp only [KS3.r0, KS3.r23, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r0, KS3.r40, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r23, KS3.r40, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E2 : (if f KS3.r0 then 1 else 0) + (if f KS3.r28 then 1 else 0)
      + (if f KS3.r35 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r0 KS3.r28 KS3.r35 KS3.r0_ne KS3.r28_ne KS3.r35_ne
    (by
      simp only [KS3.r0, KS3.r28, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r0, KS3.r35, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r28, KS3.r35, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E3 : (if f KS3.r1 then 1 else 0) + (if f KS3.r11 then 1 else 0)
      + (if f KS3.r34 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r1 KS3.r11 KS3.r34 KS3.r1_ne KS3.r11_ne KS3.r34_ne
    (by
      simp only [KS3.r1, KS3.r11, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r1, KS3.r34, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r11, KS3.r34, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E4 : (if f KS3.r1 then 1 else 0) + (if f KS3.r12 then 1 else 0)
      + (if f KS3.r33 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r1 KS3.r12 KS3.r33 KS3.r1_ne KS3.r12_ne KS3.r33_ne
    (by
      simp only [KS3.r1, KS3.r12, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r1, KS3.r33, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r12, KS3.r33, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E5 : (if f KS3.r2 then 1 else 0) + (if f KS3.r37 then 1 else 0)
      + (if f KS3.r41 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r2 KS3.r37 KS3.r41 KS3.r2_ne KS3.r37_ne KS3.r41_ne
    (by
      simp only [KS3.r2, KS3.r37, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r2, KS3.r41, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r37, KS3.r41, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E6 : (if f KS3.r3 then 1 else 0) + (if f KS3.r36 then 1 else 0)
      + (if f KS3.r42 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r3 KS3.r36 KS3.r42 KS3.r3_ne KS3.r36_ne KS3.r42_ne
    (by
      simp only [KS3.r3, KS3.r36, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r3, KS3.r42, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r36, KS3.r42, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E7 : (if f KS3.r4 then 1 else 0) + (if f KS3.r7 then 1 else 0)
      + (if f KS3.r8 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r4 KS3.r7 KS3.r8 KS3.r4_ne KS3.r7_ne KS3.r8_ne
    (by
      simp only [KS3.r4, KS3.r7, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r4, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r7, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E8 : (if f KS3.r5 then 1 else 0) + (if f KS3.r6 then 1 else 0)
      + (if f KS3.r8 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r5 KS3.r6 KS3.r8 KS3.r5_ne KS3.r6_ne KS3.r8_ne
    (by
      simp only [KS3.r5, KS3.r6, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r5, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r6, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E9 : (if f KS3.r9 then 1 else 0) + (if f KS3.r25 then 1 else 0)
      + (if f KS3.r30 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r9 KS3.r25 KS3.r30 KS3.r9_ne KS3.r25_ne KS3.r30_ne
    (by
      simp only [KS3.r9, KS3.r25, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r9, KS3.r30, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r25, KS3.r30, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E10 : (if f KS3.r10 then 1 else 0) + (if f KS3.r24 then 1 else 0)
      + (if f KS3.r29 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r10 KS3.r24 KS3.r29 KS3.r10_ne KS3.r24_ne KS3.r29_ne
    (by
      simp only [KS3.r10, KS3.r24, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r10, KS3.r29, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r24, KS3.r29, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E11 : (if f KS3.r13 then 1 else 0) + (if f KS3.r21 then 1 else 0)
      + (if f KS3.r22 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r13 KS3.r21 KS3.r22 KS3.r13_ne KS3.r21_ne KS3.r22_ne
    (by
      simp only [KS3.r13, KS3.r21, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r13, KS3.r22, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r21, KS3.r22, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E12 : (if f KS3.r16 then 1 else 0) + (if f KS3.r17 then 1 else 0)
      + (if f KS3.r18 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r16 KS3.r17 KS3.r18 KS3.r16_ne KS3.r17_ne KS3.r18_ne
    (by
      simp only [KS3.r16, KS3.r17, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r16, KS3.r18, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r17, KS3.r18, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E15 : (if f KS3.r0 then 1 else 0) + (if f KS3.r13 then 1 else 0)
      + (if f KS3.c2 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r0 KS3.r13 KS3.c2 KS3.r0_ne KS3.r13_ne KS3.c2_ne
    (by
      simp only [KS3.r0, KS3.r13, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r0, KS3.c2, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r13, KS3.c2, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E16 : (if f KS3.r0 then 1 else 0) + (if f KS3.r18 then 1 else 0)
      + (if f KS3.c3 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r0 KS3.r18 KS3.c3 KS3.r0_ne KS3.r18_ne KS3.c3_ne
    (by
      simp only [KS3.r0, KS3.r18, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r0, KS3.c3, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r18, KS3.c3, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E22 : (if f KS3.r1 then 1 else 0) + (if f KS3.r9 then 1 else 0)
      + (if f KS3.c9 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r1 KS3.r9 KS3.c9 KS3.r1_ne KS3.r9_ne KS3.c9_ne
    (by
      simp only [KS3.r1, KS3.r9, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r1, KS3.c9, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r9, KS3.c9, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E23 : (if f KS3.r1 then 1 else 0) + (if f KS3.r10 then 1 else 0)
      + (if f KS3.c10 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r1 KS3.r10 KS3.c10 KS3.r1_ne KS3.r10_ne KS3.c10_ne
    (by
      simp only [KS3.r1, KS3.r10, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r1, KS3.c10, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r10, KS3.c10, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E28 : (if f KS3.r2 then 1 else 0) + (if f KS3.r3 then 1 else 0)
      + (if f KS3.c15 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r2 KS3.r3 KS3.c15 KS3.r2_ne KS3.r3_ne KS3.c15_ne
    (by
      simp only [KS3.r2, KS3.r3, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r2, KS3.c15, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r3, KS3.c15, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E29 : (if f KS3.r2 then 1 else 0) + (if f KS3.r8 then 1 else 0)
      + (if f KS3.c16 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r2 KS3.r8 KS3.c16 KS3.r2_ne KS3.r8_ne KS3.c16_ne
    (by
      simp only [KS3.r2, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r2, KS3.c16, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r8, KS3.c16, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E32 : (if f KS3.r3 then 1 else 0) + (if f KS3.r8 then 1 else 0)
      + (if f KS3.c19 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r3 KS3.r8 KS3.c19 KS3.r3_ne KS3.r8_ne KS3.c19_ne
    (by
      simp only [KS3.r3, KS3.r8, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r3, KS3.c19, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r8, KS3.c19, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E37 : (if f KS3.r4 then 1 else 0) + (if f KS3.r25 then 1 else 0)
      + (if f KS3.c24 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r4 KS3.r25 KS3.c24 KS3.r4_ne KS3.r25_ne KS3.c24_ne
    (by
      simp only [KS3.r4, KS3.r25, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r4, KS3.c24, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r25, KS3.c24, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E38 : (if f KS3.r4 then 1 else 0) + (if f KS3.r29 then 1 else 0)
      + (if f KS3.c25 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r4 KS3.r29 KS3.c25 KS3.r4_ne KS3.r29_ne KS3.c25_ne
    (by
      simp only [KS3.r4, KS3.r29, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r4, KS3.c25, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r29, KS3.c25, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E41 : (if f KS3.r5 then 1 else 0) + (if f KS3.r24 then 1 else 0)
      + (if f KS3.c28 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r5 KS3.r24 KS3.c28 KS3.r5_ne KS3.r24_ne KS3.c28_ne
    (by
      simp only [KS3.r5, KS3.r24, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r5, KS3.c28, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r24, KS3.c28, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E42 : (if f KS3.r5 then 1 else 0) + (if f KS3.r30 then 1 else 0)
      + (if f KS3.c29 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r5 KS3.r30 KS3.c29 KS3.r5_ne KS3.r30_ne KS3.c29_ne
    (by
      simp only [KS3.r5, KS3.r30, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r5, KS3.c29, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r30, KS3.c29, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E44 : (if f KS3.r6 then 1 else 0) + (if f KS3.r17 then 1 else 0)
      + (if f KS3.c31 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r6 KS3.r17 KS3.c31 KS3.r6_ne KS3.r17_ne KS3.c31_ne
    (by
      simp only [KS3.r6, KS3.r17, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r6, KS3.c31, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r17, KS3.c31, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E45 : (if f KS3.r6 then 1 else 0) + (if f KS3.r21 then 1 else 0)
      + (if f KS3.c32 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r6 KS3.r21 KS3.c32 KS3.r6_ne KS3.r21_ne KS3.c32_ne
    (by
      simp only [KS3.r6, KS3.r21, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r6, KS3.c32, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r21, KS3.c32, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E47 : (if f KS3.r7 then 1 else 0) + (if f KS3.r16 then 1 else 0)
      + (if f KS3.c34 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r7 KS3.r16 KS3.c34 KS3.r7_ne KS3.r16_ne KS3.c34_ne
    (by
      simp only [KS3.r7, KS3.r16, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r7, KS3.c34, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r16, KS3.c34, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E48 : (if f KS3.r7 then 1 else 0) + (if f KS3.r22 then 1 else 0)
      + (if f KS3.c35 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r7 KS3.r22 KS3.c35 KS3.r7_ne KS3.r22_ne KS3.c35_ne
    (by
      simp only [KS3.r7, KS3.r22, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r7, KS3.c35, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r22, KS3.c35, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E49 : (if f KS3.r9 then 1 else 0) + (if f KS3.r10 then 1 else 0)
      + (if f KS3.c36 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r9 KS3.r10 KS3.c36 KS3.r9_ne KS3.r10_ne KS3.c36_ne
    (by
      simp only [KS3.r9, KS3.r10, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r9, KS3.c36, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r10, KS3.c36, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E55 : (if f KS3.r11 then 1 else 0) + (if f KS3.r37 then 1 else 0)
      + (if f KS3.c42 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r11 KS3.r37 KS3.c42 KS3.r11_ne KS3.r37_ne KS3.c42_ne
    (by
      simp only [KS3.r11, KS3.r37, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r11, KS3.c42, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r37, KS3.c42, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E56 : (if f KS3.r11 then 1 else 0) + (if f KS3.r42 then 1 else 0)
      + (if f KS3.c43 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r11 KS3.r42 KS3.c43 KS3.r11_ne KS3.r42_ne KS3.c43_ne
    (by
      simp only [KS3.r11, KS3.r42, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r11, KS3.c43, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r42, KS3.c43, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E58 : (if f KS3.r12 then 1 else 0) + (if f KS3.r36 then 1 else 0)
      + (if f KS3.c45 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r12 KS3.r36 KS3.c45 KS3.r12_ne KS3.r36_ne KS3.c45_ne
    (by
      simp only [KS3.r12, KS3.r36, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r12, KS3.c45, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r36, KS3.c45, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E59 : (if f KS3.r12 then 1 else 0) + (if f KS3.r41 then 1 else 0)
      + (if f KS3.c46 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r12 KS3.r41 KS3.c46 KS3.r12_ne KS3.r41_ne KS3.c46_ne
    (by
      simp only [KS3.r12, KS3.r41, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r12, KS3.c46, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r41, KS3.c46, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E60 : (if f KS3.r13 then 1 else 0) + (if f KS3.r18 then 1 else 0)
      + (if f KS3.c47 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r13 KS3.r18 KS3.c47 KS3.r13_ne KS3.r18_ne KS3.c47_ne
    (by
      simp only [KS3.r13, KS3.r18, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r13, KS3.c47, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r18, KS3.c47, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E65 : (if f KS3.r16 then 1 else 0) + (if f KS3.r34 then 1 else 0)
      + (if f KS3.c52 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r16 KS3.r34 KS3.c52 KS3.r16_ne KS3.r34_ne KS3.c52_ne
    (by
      simp only [KS3.r16, KS3.r34, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r16, KS3.c52, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r34, KS3.c52, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E67 : (if f KS3.r17 then 1 else 0) + (if f KS3.r33 then 1 else 0)
      + (if f KS3.c54 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r17 KS3.r33 KS3.c54 KS3.r17_ne KS3.r33_ne KS3.c54_ne
    (by
      simp only [KS3.r17, KS3.r33, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r17, KS3.c54, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r33, KS3.c54, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E69 : (if f KS3.r21 then 1 else 0) + (if f KS3.r34 then 1 else 0)
      + (if f KS3.c56 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r21 KS3.r34 KS3.c56 KS3.r21_ne KS3.r34_ne KS3.c56_ne
    (by
      simp only [KS3.r21, KS3.r34, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r21, KS3.c56, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r34, KS3.c56, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E70 : (if f KS3.r22 then 1 else 0) + (if f KS3.r33 then 1 else 0)
      + (if f KS3.c57 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r22 KS3.r33 KS3.c57 KS3.r22_ne KS3.r33_ne KS3.c57_ne
    (by
      simp only [KS3.r22, KS3.r33, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r22, KS3.c57, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r33, KS3.c57, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E72 : (if f KS3.r23 then 1 else 0) + (if f KS3.r41 then 1 else 0)
      + (if f KS3.c59 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r23 KS3.r41 KS3.c59 KS3.r23_ne KS3.r41_ne KS3.c59_ne
    (by
      simp only [KS3.r23, KS3.r41, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r23, KS3.c59, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r41, KS3.c59, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E73 : (if f KS3.r23 then 1 else 0) + (if f KS3.r42 then 1 else 0)
      + (if f KS3.c60 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r23 KS3.r42 KS3.c60 KS3.r23_ne KS3.r42_ne KS3.c60_ne
    (by
      simp only [KS3.r23, KS3.r42, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r23, KS3.c60, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r42, KS3.c60, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E75 : (if f KS3.r24 then 1 else 0) + (if f KS3.r40 then 1 else 0)
      + (if f KS3.c62 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r24 KS3.r40 KS3.c62 KS3.r24_ne KS3.r40_ne KS3.c62_ne
    (by
      simp only [KS3.r24, KS3.r40, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r24, KS3.c62, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r40, KS3.c62, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E77 : (if f KS3.r25 then 1 else 0) + (if f KS3.r40 then 1 else 0)
      + (if f KS3.c64 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r25 KS3.r40 KS3.c64 KS3.r25_ne KS3.r40_ne KS3.c64_ne
    (by
      simp only [KS3.r25, KS3.r40, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r25, KS3.c64, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r40, KS3.c64, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E79 : (if f KS3.r28 then 1 else 0) + (if f KS3.r36 then 1 else 0)
      + (if f KS3.c66 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r28 KS3.r36 KS3.c66 KS3.r28_ne KS3.r36_ne KS3.c66_ne
    (by
      simp only [KS3.r28, KS3.r36, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r28, KS3.c66, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r36, KS3.c66, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
  have E80 : (if f KS3.r28 then 1 else 0) + (if f KS3.r37 then 1 else 0)
      + (if f KS3.c67 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r28 KS3.r37 KS3.c67 KS3.r28_ne KS3.r37_ne KS3.c67_ne
    (by
      simp only [KS3.r28, KS3.r37, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r28, KS3.c67, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r37, KS3.c67, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
  have E81 : (if f KS3.r29 then 1 else 0) + (if f KS3.r35 then 1 else 0)
      + (if f KS3.c68 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r29 KS3.r35 KS3.c68 KS3.r29_ne KS3.r35_ne KS3.c68_ne
    (by
      simp only [KS3.r29, KS3.r35, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r29, KS3.c68, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (-1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r35, KS3.c68, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  have E82 : (if f KS3.r30 then 1 else 0) + (if f KS3.r35 then 1 else 0)
      + (if f KS3.c69 then 1 else 0) = (1 : ℕ) :=
    H3 KS3.r30 KS3.r35 KS3.c69 KS3.r30_ne KS3.r35_ne KS3.c69_ne
    (by
      simp only [KS3.r30, KS3.r35, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
    (by
      simp only [KS3.r30, KS3.c69, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linear_combination (1 : ℝ) * KS3.sqrt2_mul_self)
    (by
      simp only [KS3.r35, KS3.c69, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)
  cases h_r0 : f KS3.r0 with
  | false =>
    cases h_r1 : f KS3.r1 with
    | false =>
      have h_r8 : f KS3.r8 = true := KS3.tri_ff01 E0 h_r0 h_r1
      have h_r4 : f KS3.r4 = false := (KS3.tri_true2 E7 h_r8).1
      have h_r7 : f KS3.r7 = false := (KS3.tri_true2 E7 h_r8).2
      have h_r5 : f KS3.r5 = false := (KS3.tri_true2 E8 h_r8).1
      have h_r6 : f KS3.r6 = false := (KS3.tri_true2 E8 h_r8).2
      have h_r2 : f KS3.r2 = false := (KS3.tri_true1 E29 h_r8).1
      have h_r3 : f KS3.r3 = false := (KS3.tri_true1 E32 h_r8).1
      cases h_r23 : f KS3.r23 with
      | false =>
        have h_r40 : f KS3.r40 = true := KS3.tri_ff01 E1 h_r0 h_r23
        have h_r24 : f KS3.r24 = false := (KS3.tri_true1 E75 h_r40).1
        have h_r25 : f KS3.r25 = false := (KS3.tri_true1 E77 h_r40).1
        cases h_r28 : f KS3.r28 with
        | false =>
          have h_r35 : f KS3.r35 = true := KS3.tri_ff01 E2 h_r0 h_r28
          have h_r29 : f KS3.r29 = false := (KS3.tri_true1 E81 h_r35).1
          have h_r30 : f KS3.r30 = false := (KS3.tri_true1 E82 h_r35).1
          have h_r9 : f KS3.r9 = true := KS3.tri_ff12 E9 h_r25 h_r30
          have h_r10 : f KS3.r10 = true := KS3.tri_ff12 E10 h_r24 h_r29
          exact KS3.tri_not2_01 E49 h_r9 h_r10
        | true =>
          have h_r35 : f KS3.r35 = false := (KS3.tri_true1 E2 h_r28).2
          have h_r36 : f KS3.r36 = false := (KS3.tri_true0 E79 h_r28).1
          have h_r37 : f KS3.r37 = false := (KS3.tri_true0 E80 h_r28).1
          have h_r41 : f KS3.r41 = true := KS3.tri_ff01 E5 h_r2 h_r37
          have h_r42 : f KS3.r42 = true := KS3.tri_ff01 E6 h_r3 h_r36
          have h_r11 : f KS3.r11 = false := (KS3.tri_true1 E56 h_r42).1
          have h_r12 : f KS3.r12 = false := (KS3.tri_true1 E59 h_r41).1
          have h_r34 : f KS3.r34 = true := KS3.tri_ff01 E3 h_r1 h_r11
          have h_r33 : f KS3.r33 = true := KS3.tri_ff01 E4 h_r1 h_r12
          have h_r16 : f KS3.r16 = false := (KS3.tri_true1 E65 h_r34).1
          have h_r17 : f KS3.r17 = false := (KS3.tri_true1 E67 h_r33).1
          have h_r21 : f KS3.r21 = false := (KS3.tri_true1 E69 h_r34).1
          have h_r22 : f KS3.r22 = false := (KS3.tri_true1 E70 h_r33).1
          have h_r13 : f KS3.r13 = true := KS3.tri_ff12 E11 h_r21 h_r22
          have h_r18 : f KS3.r18 = true := KS3.tri_ff01 E12 h_r16 h_r17
          exact KS3.tri_not2_01 E60 h_r13 h_r18
      | true =>
        have h_r40 : f KS3.r40 = false := (KS3.tri_true1 E1 h_r23).2
        have h_r41 : f KS3.r41 = false := (KS3.tri_true0 E72 h_r23).1
        have h_r42 : f KS3.r42 = false := (KS3.tri_true0 E73 h_r23).1
        have h_r37 : f KS3.r37 = true := KS3.tri_ff02 E5 h_r2 h_r41
        have h_r36 : f KS3.r36 = true := KS3.tri_ff02 E6 h_r3 h_r42
        have h_r11 : f KS3.r11 = false := (KS3.tri_true1 E55 h_r37).1
        have h_r12 : f KS3.r12 = false := (KS3.tri_true1 E58 h_r36).1
        have h_r28 : f KS3.r28 = false := (KS3.tri_true1 E79 h_r36).1
        have h_r35 : f KS3.r35 = true := KS3.tri_ff01 E2 h_r0 h_r28
        have h_r34 : f KS3.r34 = true := KS3.tri_ff01 E3 h_r1 h_r11
        have h_r33 : f KS3.r33 = true := KS3.tri_ff01 E4 h_r1 h_r12
        have h_r16 : f KS3.r16 = false := (KS3.tri_true1 E65 h_r34).1
        have h_r17 : f KS3.r17 = false := (KS3.tri_true1 E67 h_r33).1
        have h_r21 : f KS3.r21 = false := (KS3.tri_true1 E69 h_r34).1
        have h_r22 : f KS3.r22 = false := (KS3.tri_true1 E70 h_r33).1
        have h_r29 : f KS3.r29 = false := (KS3.tri_true1 E81 h_r35).1
        have h_r30 : f KS3.r30 = false := (KS3.tri_true1 E82 h_r35).1
        have h_r13 : f KS3.r13 = true := KS3.tri_ff12 E11 h_r21 h_r22
        have h_r18 : f KS3.r18 = true := KS3.tri_ff01 E12 h_r16 h_r17
        exact KS3.tri_not2_01 E60 h_r13 h_r18
    | true =>
      have h_r8 : f KS3.r8 = false := (KS3.tri_true1 E0 h_r1).2
      have h_r11 : f KS3.r11 = false := (KS3.tri_true0 E3 h_r1).1
      have h_r34 : f KS3.r34 = false := (KS3.tri_true0 E3 h_r1).2
      have h_r12 : f KS3.r12 = false := (KS3.tri_true0 E4 h_r1).1
      have h_r33 : f KS3.r33 = false := (KS3.tri_true0 E4 h_r1).2
      have h_r9 : f KS3.r9 = false := (KS3.tri_true0 E22 h_r1).1
      have h_r10 : f KS3.r10 = false := (KS3.tri_true0 E23 h_r1).1
      cases h_r23 : f KS3.r23 with
      | false =>
        have h_r40 : f KS3.r40 = true := KS3.tri_ff01 E1 h_r0 h_r23
        have h_r24 : f KS3.r24 = false := (KS3.tri_true1 E75 h_r40).1
        have h_r25 : f KS3.r25 = false := (KS3.tri_true1 E77 h_r40).1
        have h_r30 : f KS3.r30 = true := KS3.tri_ff01 E9 h_r9 h_r25
        have h_r29 : f KS3.r29 = true := KS3.tri_ff01 E10 h_r10 h_r24
        have h_r4 : f KS3.r4 = false := (KS3.tri_true1 E38 h_r29).1
        have h_r5 : f KS3.r5 = false := (KS3.tri_true1 E42 h_r30).1
        have h_r35 : f KS3.r35 = false := (KS3.tri_true0 E81 h_r29).1
        have h_r28 : f KS3.r28 = true := KS3.tri_ff02 E2 h_r0 h_r35
        have h_r7 : f KS3.r7 = true := KS3.tri_ff02 E7 h_r4 h_r8
        have h_r6 : f KS3.r6 = true := KS3.tri_ff02 E8 h_r5 h_r8
        have h_r17 : f KS3.r17 = false := (KS3.tri_true0 E44 h_r6).1
        have h_r21 : f KS3.r21 = false := (KS3.tri_true0 E45 h_r6).1
        have h_r16 : f KS3.r16 = false := (KS3.tri_true0 E47 h_r7).1
        have h_r22 : f KS3.r22 = false := (KS3.tri_true0 E48 h_r7).1
        have h_r36 : f KS3.r36 = false := (KS3.tri_true0 E79 h_r28).1
        have h_r37 : f KS3.r37 = false := (KS3.tri_true0 E80 h_r28).1
        have h_r13 : f KS3.r13 = true := KS3.tri_ff12 E11 h_r21 h_r22
        have h_r18 : f KS3.r18 = true := KS3.tri_ff01 E12 h_r16 h_r17
        exact KS3.tri_not2_01 E60 h_r13 h_r18
      | true =>
        have h_r40 : f KS3.r40 = false := (KS3.tri_true1 E1 h_r23).2
        have h_r41 : f KS3.r41 = false := (KS3.tri_true0 E72 h_r23).1
        have h_r42 : f KS3.r42 = false := (KS3.tri_true0 E73 h_r23).1
        cases h_r28 : f KS3.r28 with
        | false =>
          have h_r35 : f KS3.r35 = true := KS3.tri_ff01 E2 h_r0 h_r28
          have h_r29 : f KS3.r29 = false := (KS3.tri_true1 E81 h_r35).1
          have h_r30 : f KS3.r30 = false := (KS3.tri_true1 E82 h_r35).1
          have h_r25 : f KS3.r25 = true := KS3.tri_ff02 E9 h_r9 h_r30
          have h_r24 : f KS3.r24 = true := KS3.tri_ff02 E10 h_r10 h_r29
          have h_r4 : f KS3.r4 = false := (KS3.tri_true1 E37 h_r25).1
          have h_r5 : f KS3.r5 = false := (KS3.tri_true1 E41 h_r24).1
          have h_r7 : f KS3.r7 = true := KS3.tri_ff02 E7 h_r4 h_r8
          have h_r6 : f KS3.r6 = true := KS3.tri_ff02 E8 h_r5 h_r8
          have h_r17 : f KS3.r17 = false := (KS3.tri_true0 E44 h_r6).1
          have h_r21 : f KS3.r21 = false := (KS3.tri_true0 E45 h_r6).1
          have h_r16 : f KS3.r16 = false := (KS3.tri_true0 E47 h_r7).1
          have h_r22 : f KS3.r22 = false := (KS3.tri_true0 E48 h_r7).1
          have h_r13 : f KS3.r13 = true := KS3.tri_ff12 E11 h_r21 h_r22
          have h_r18 : f KS3.r18 = true := KS3.tri_ff01 E12 h_r16 h_r17
          exact KS3.tri_not2_01 E60 h_r13 h_r18
        | true =>
          have h_r35 : f KS3.r35 = false := (KS3.tri_true1 E2 h_r28).2
          have h_r36 : f KS3.r36 = false := (KS3.tri_true0 E79 h_r28).1
          have h_r37 : f KS3.r37 = false := (KS3.tri_true0 E80 h_r28).1
          have h_r2 : f KS3.r2 = true := KS3.tri_ff12 E5 h_r37 h_r41
          have h_r3 : f KS3.r3 = true := KS3.tri_ff12 E6 h_r36 h_r42
          exact KS3.tri_not2_01 E28 h_r2 h_r3
  | true =>
    have h_r1 : f KS3.r1 = false := (KS3.tri_true0 E0 h_r0).1
    have h_r8 : f KS3.r8 = false := (KS3.tri_true0 E0 h_r0).2
    have h_r23 : f KS3.r23 = false := (KS3.tri_true0 E1 h_r0).1
    have h_r40 : f KS3.r40 = false := (KS3.tri_true0 E1 h_r0).2
    have h_r28 : f KS3.r28 = false := (KS3.tri_true0 E2 h_r0).1
    have h_r35 : f KS3.r35 = false := (KS3.tri_true0 E2 h_r0).2
    have h_r13 : f KS3.r13 = false := (KS3.tri_true0 E15 h_r0).1
    have h_r18 : f KS3.r18 = false := (KS3.tri_true0 E16 h_r0).1
    cases h_r11 : f KS3.r11 with
    | false =>
      have h_r34 : f KS3.r34 = true := KS3.tri_ff01 E3 h_r1 h_r11
      have h_r16 : f KS3.r16 = false := (KS3.tri_true1 E65 h_r34).1
      have h_r21 : f KS3.r21 = false := (KS3.tri_true1 E69 h_r34).1
      have h_r22 : f KS3.r22 = true := KS3.tri_ff01 E11 h_r13 h_r21
      have h_r17 : f KS3.r17 = true := KS3.tri_ff02 E12 h_r16 h_r18
      have h_r6 : f KS3.r6 = false := (KS3.tri_true1 E44 h_r17).1
      have h_r7 : f KS3.r7 = false := (KS3.tri_true1 E48 h_r22).1
      have h_r33 : f KS3.r33 = false := (KS3.tri_true0 E67 h_r17).1
      have h_r12 : f KS3.r12 = true := KS3.tri_ff02 E4 h_r1 h_r33
      have h_r4 : f KS3.r4 = true := KS3.tri_ff12 E7 h_r7 h_r8
      have h_r5 : f KS3.r5 = true := KS3.tri_ff12 E8 h_r6 h_r8
      have h_r25 : f KS3.r25 = false := (KS3.tri_true0 E37 h_r4).1
      have h_r29 : f KS3.r29 = false := (KS3.tri_true0 E38 h_r4).1
      have h_r24 : f KS3.r24 = false := (KS3.tri_true0 E41 h_r5).1
      have h_r30 : f KS3.r30 = false := (KS3.tri_true0 E42 h_r5).1
      have h_r36 : f KS3.r36 = false := (KS3.tri_true0 E58 h_r12).1
      have h_r41 : f KS3.r41 = false := (KS3.tri_true0 E59 h_r12).1
      have h_r9 : f KS3.r9 = true := KS3.tri_ff12 E9 h_r25 h_r30
      have h_r10 : f KS3.r10 = true := KS3.tri_ff12 E10 h_r24 h_r29
      exact KS3.tri_not2_01 E49 h_r9 h_r10
    | true =>
      have h_r34 : f KS3.r34 = false := (KS3.tri_true1 E3 h_r11).2
      have h_r37 : f KS3.r37 = false := (KS3.tri_true0 E55 h_r11).1
      have h_r42 : f KS3.r42 = false := (KS3.tri_true0 E56 h_r11).1
      cases h_r12 : f KS3.r12 with
      | false =>
        have h_r33 : f KS3.r33 = true := KS3.tri_ff01 E4 h_r1 h_r12
        have h_r17 : f KS3.r17 = false := (KS3.tri_true1 E67 h_r33).1
        have h_r22 : f KS3.r22 = false := (KS3.tri_true1 E70 h_r33).1
        have h_r21 : f KS3.r21 = true := KS3.tri_ff02 E11 h_r13 h_r22
        have h_r16 : f KS3.r16 = true := KS3.tri_ff12 E12 h_r17 h_r18
        have h_r6 : f KS3.r6 = false := (KS3.tri_true1 E45 h_r21).1
        have h_r7 : f KS3.r7 = false := (KS3.tri_true1 E47 h_r16).1
        have h_r4 : f KS3.r4 = true := KS3.tri_ff12 E7 h_r7 h_r8
        have h_r5 : f KS3.r5 = true := KS3.tri_ff12 E8 h_r6 h_r8
        have h_r25 : f KS3.r25 = false := (KS3.tri_true0 E37 h_r4).1
        have h_r29 : f KS3.r29 = false := (KS3.tri_true0 E38 h_r4).1
        have h_r24 : f KS3.r24 = false := (KS3.tri_true0 E41 h_r5).1
        have h_r30 : f KS3.r30 = false := (KS3.tri_true0 E42 h_r5).1
        have h_r9 : f KS3.r9 = true := KS3.tri_ff12 E9 h_r25 h_r30
        have h_r10 : f KS3.r10 = true := KS3.tri_ff12 E10 h_r24 h_r29
        exact KS3.tri_not2_01 E49 h_r9 h_r10
      | true =>
        have h_r33 : f KS3.r33 = false := (KS3.tri_true1 E4 h_r12).2
        have h_r36 : f KS3.r36 = false := (KS3.tri_true0 E58 h_r12).1
        have h_r41 : f KS3.r41 = false := (KS3.tri_true0 E59 h_r12).1
        have h_r2 : f KS3.r2 = true := KS3.tri_ff12 E5 h_r37 h_r41
        have h_r3 : f KS3.r3 = true := KS3.tri_ff12 E6 h_r36 h_r42
        exact KS3.tri_not2_01 E28 h_r2 h_r3

end Frontier

/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Dim3

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
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

namespace Frontier

/-- Shorthand for the four dimensional real Hilbert space. -/
abbrev KSSpace := EuclideanSpace ℝ (Fin 4)

namespace KS

/-- A vector with a nonzero coordinate is nonzero. -/
