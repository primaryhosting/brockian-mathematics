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


theorem kochen_specker_dim_four :
    ¬ ∃ f : KSSpace → Bool,
        ∀ v : Fin 4 → KSSpace,
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if f (v i) then (1 : ℕ) else 0) = 1 := by
  rintro ⟨f, hf⟩
  -- From the hypothesis: any orthogonal frame given by four vectors carries exactly one `1`.
  have H : ∀ a b c d : KSSpace, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
      inner ℝ a b = (0 : ℝ) → inner ℝ a c = (0 : ℝ) → inner ℝ a d = (0 : ℝ) →
      inner ℝ b c = (0 : ℝ) → inner ℝ b d = (0 : ℝ) → inner ℝ c d = (0 : ℝ) →
      (if f a then 1 else 0) + (if f b then 1 else 0) + (if f c then 1 else 0)
        + (if f d then 1 else 0) = (1 : ℕ) := by
    intro a b c d ha hb hc hd hab hac had hbc hbd hcd
    have hba : inner ℝ b a = (0 : ℝ) := by rw [real_inner_comm]; exact hab
    have hca : inner ℝ c a = (0 : ℝ) := by rw [real_inner_comm]; exact hac
    have hda : inner ℝ d a = (0 : ℝ) := by rw [real_inner_comm]; exact had
    have hcb : inner ℝ c b = (0 : ℝ) := by rw [real_inner_comm]; exact hbc
    have hdb : inner ℝ d b = (0 : ℝ) := by rw [real_inner_comm]; exact hbd
    have hdc : inner ℝ d c = (0 : ℝ) := by rw [real_inner_comm]; exact hcd
    have key := hf ![a, b, c, d]
      (by intro i; fin_cases i <;> simpa using ‹_›)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    rw [Fin.sum_univ_four] at key
    simpa using key
  -- The nine bases of the Kochen–Specker set.
  have e1 := H KS.u1 KS.u2 KS.u3 KS.u4
    (KS.ne_zero_of_coord 3 (by simp [KS.u1])) (KS.ne_zero_of_coord 2 (by simp [KS.u2]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u3])) (KS.ne_zero_of_coord 0 (by simp [KS.u4]))
    (by simp [KS.u1, KS.u2, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u1, KS.u3, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u1, KS.u4, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u2, KS.u3, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u2, KS.u4, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u3, KS.u4, PiLp.inner_apply, Fin.sum_univ_four])
  have e2 := H KS.u1 KS.u5 KS.u6 KS.u7
    (KS.ne_zero_of_coord 3 (by simp [KS.u1])) (KS.ne_zero_of_coord 1 (by simp [KS.u5]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u6])) (KS.ne_zero_of_coord 0 (by simp [KS.u7]))
    (by simp [KS.u1, KS.u5, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u1, KS.u6, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u1, KS.u7, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u5, KS.u6, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u5, KS.u7, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u6, KS.u7, PiLp.inner_apply, Fin.sum_univ_four])
  have e3 := H KS.u8 KS.u9 KS.u3 KS.u10
    (KS.ne_zero_of_coord 0 (by simp [KS.u8])) (KS.ne_zero_of_coord 0 (by simp [KS.u9]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u3])) (KS.ne_zero_of_coord 2 (by simp [KS.u10]))
    (by simp [KS.u8, KS.u9, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u8, KS.u3, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u8, KS.u10, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u9, KS.u3, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u9, KS.u10, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u3, KS.u10, PiLp.inner_apply, Fin.sum_univ_four])
  have e4 := H KS.u8 KS.u11 KS.u7 KS.u12
    (KS.ne_zero_of_coord 0 (by simp [KS.u8])) (KS.ne_zero_of_coord 0 (by simp [KS.u11]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u7])) (KS.ne_zero_of_coord 1 (by simp [KS.u12]))
    (by simp [KS.u8, KS.u11, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u8, KS.u7, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u8, KS.u12, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u11, KS.u7, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u11, KS.u12, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u7, KS.u12, PiLp.inner_apply, Fin.sum_univ_four])
  have e5 := H KS.u2 KS.u5 KS.u13 KS.u14
    (KS.ne_zero_of_coord 2 (by simp [KS.u2])) (KS.ne_zero_of_coord 1 (by simp [KS.u5]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u13])) (KS.ne_zero_of_coord 0 (by simp [KS.u14]))
    (by simp [KS.u2, KS.u5, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u2, KS.u13, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u2, KS.u14, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u5, KS.u13, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u5, KS.u14, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u13, KS.u14, PiLp.inner_apply, Fin.sum_univ_four])
  have e6 := H KS.u9 KS.u11 KS.u14 KS.u15
    (KS.ne_zero_of_coord 0 (by simp [KS.u9])) (KS.ne_zero_of_coord 0 (by simp [KS.u11]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u14])) (KS.ne_zero_of_coord 1 (by simp [KS.u15]))
    (by simp [KS.u9, KS.u11, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u9, KS.u14, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u9, KS.u15, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u11, KS.u14, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u11, KS.u15, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u14, KS.u15, PiLp.inner_apply, Fin.sum_univ_four])
  have e7 := H KS.u16 KS.u17 KS.u4 KS.u10
    (KS.ne_zero_of_coord 0 (by simp [KS.u16])) (KS.ne_zero_of_coord 0 (by simp [KS.u17]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u4])) (KS.ne_zero_of_coord 2 (by simp [KS.u10]))
    (by simp [KS.u16, KS.u17, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u16, KS.u4, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u16, KS.u10, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u17, KS.u4, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u17, KS.u10, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u4, KS.u10, PiLp.inner_apply, Fin.sum_univ_four])
  have e8 := H KS.u16 KS.u18 KS.u6 KS.u12
    (KS.ne_zero_of_coord 0 (by simp [KS.u16])) (KS.ne_zero_of_coord 0 (by simp [KS.u18]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u6])) (KS.ne_zero_of_coord 1 (by simp [KS.u12]))
    (by simp [KS.u16, KS.u18, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u16, KS.u6, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u16, KS.u12, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u18, KS.u6, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u18, KS.u12, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u6, KS.u12, PiLp.inner_apply, Fin.sum_univ_four])
  have e9 := H KS.u17 KS.u18 KS.u13 KS.u15
    (KS.ne_zero_of_coord 0 (by simp [KS.u17])) (KS.ne_zero_of_coord 0 (by simp [KS.u18]))
    (KS.ne_zero_of_coord 0 (by simp [KS.u13])) (KS.ne_zero_of_coord 1 (by simp [KS.u15]))
    (by simp [KS.u17, KS.u18, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u17, KS.u13, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u17, KS.u15, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u18, KS.u13, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u18, KS.u15, PiLp.inner_apply, Fin.sum_univ_four])
    (by simp [KS.u13, KS.u15, PiLp.inner_apply, Fin.sum_univ_four])
  -- Each vector occurs in exactly two bases, so the nine equations sum to `9 = 2 * k`.
  omega

namespace KS

/-- The isometric embedding of `ℝᵐ` into `ℝⁿ` determined by an injection `σ : Fin m → Fin n`. -/
