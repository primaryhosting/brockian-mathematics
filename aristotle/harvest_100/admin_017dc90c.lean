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

theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-! ### The rays of the configuration -/

noncomputable def c2 : V3 := !₂[((-1) : ℝ), 1, 0]
noncomputable def c3 : V3 := !₂[(1 : ℝ), 1, 0]
noncomputable def c9 : V3 := !₂[(1 : ℝ), 0, (-1)]
noncomputable def c10 : V3 := !₂[((-1) : ℝ), 0, (-1)]
noncomputable def c15 : V3 := !₂[((-2) : ℝ), 0, 0]
noncomputable def c16 : V3 := !₂[(0 : ℝ), 1, (-1)]
noncomputable def c19 : V3 := !₂[(0 : ℝ), (-1), (-1)]
noncomputable def c24 : V3 := !₂[((-3) : ℝ), Real.sqrt 2, (-1)]
noncomputable def c25 : V3 := !₂[(3 : ℝ), Real.sqrt 2, (-1)]
noncomputable def c28 : V3 := !₂[(3 : ℝ), -Real.sqrt 2, (-1)]
noncomputable def c29 : V3 := !₂[((-3) : ℝ), -Real.sqrt 2, (-1)]
noncomputable def c31 : V3 := !₂[((-3) : ℝ), 1, -Real.sqrt 2]
noncomputable def c32 : V3 := !₂[(3 : ℝ), 1, -Real.sqrt 2]
noncomputable def c34 : V3 := !₂[(3 : ℝ), (-1), -Real.sqrt 2]
noncomputable def c35 : V3 := !₂[((-3) : ℝ), (-1), -Real.sqrt 2]
noncomputable def c36 : V3 := !₂[(0 : ℝ), 2, 0]
noncomputable def c42 : V3 := !₂[(-Real.sqrt 2 : ℝ), 3, 1]
noncomputable def c43 : V3 := !₂[(Real.sqrt 2 : ℝ), 3, (-1)]
noncomputable def c45 : V3 := !₂[(Real.sqrt 2 : ℝ), (-3), 1]
noncomputable def c46 : V3 := !₂[(-Real.sqrt 2 : ℝ), (-3), (-1)]
noncomputable def c47 : V3 := !₂[(0 : ℝ), 0, (-2)]
noncomputable def c52 : V3 := !₂[((-1) : ℝ), 3, -Real.sqrt 2]
noncomputable def c54 : V3 := !₂[(1 : ℝ), (-3), -Real.sqrt 2]
noncomputable def c56 : V3 := !₂[(1 : ℝ), 3, Real.sqrt 2]
noncomputable def c57 : V3 := !₂[((-1) : ℝ), (-3), Real.sqrt 2]
noncomputable def c59 : V3 := !₂[(Real.sqrt 2 : ℝ), (-1), (-3)]
noncomputable def c60 : V3 := !₂[(-Real.sqrt 2 : ℝ), 1, (-3)]
noncomputable def c62 : V3 := !₂[(1 : ℝ), Real.sqrt 2, (-3)]
noncomputable def c64 : V3 := !₂[((-1) : ℝ), -Real.sqrt 2, (-3)]
noncomputable def c66 : V3 := !₂[(-Real.sqrt 2 : ℝ), (-1), 3]
noncomputable def c67 : V3 := !₂[(Real.sqrt 2 : ℝ), 1, 3]
noncomputable def c68 : V3 := !₂[((-1) : ℝ), Real.sqrt 2, 3]
noncomputable def c69 : V3 := !₂[(1 : ℝ), -Real.sqrt 2, 3]
noncomputable def r0 : V3 := !₂[(0 : ℝ), 0, 1]
noncomputable def r1 : V3 := !₂[(0 : ℝ), 1, 0]
noncomputable def r2 : V3 := !₂[(0 : ℝ), 1, 1]
noncomputable def r3 : V3 := !₂[(0 : ℝ), 1, (-1)]
noncomputable def r4 : V3 := !₂[(0 : ℝ), 1, Real.sqrt 2]
noncomputable def r5 : V3 := !₂[(0 : ℝ), 1, -Real.sqrt 2]
noncomputable def r6 : V3 := !₂[(0 : ℝ), Real.sqrt 2, 1]
noncomputable def r7 : V3 := !₂[(0 : ℝ), Real.sqrt 2, (-1)]
noncomputable def r8 : V3 := !₂[(1 : ℝ), 0, 0]
noncomputable def r9 : V3 := !₂[(1 : ℝ), 0, 1]
noncomputable def r10 : V3 := !₂[(1 : ℝ), 0, (-1)]
noncomputable def r11 : V3 := !₂[(1 : ℝ), 0, Real.sqrt 2]
noncomputable def r12 : V3 := !₂[(1 : ℝ), 0, -Real.sqrt 2]
noncomputable def r13 : V3 := !₂[(1 : ℝ), 1, 0]
noncomputable def r16 : V3 := !₂[(1 : ℝ), 1, Real.sqrt 2]
noncomputable def r17 : V3 := !₂[(1 : ℝ), 1, -Real.sqrt 2]
noncomputable def r18 : V3 := !₂[(1 : ℝ), (-1), 0]
noncomputable def r21 : V3 := !₂[(1 : ℝ), (-1), Real.sqrt 2]
noncomputable def r22 : V3 := !₂[(1 : ℝ), (-1), -Real.sqrt 2]
noncomputable def r23 : V3 := !₂[(1 : ℝ), Real.sqrt 2, 0]
noncomputable def r24 : V3 := !₂[(1 : ℝ), Real.sqrt 2, 1]
noncomputable def r25 : V3 := !₂[(1 : ℝ), Real.sqrt 2, (-1)]
noncomputable def r28 : V3 := !₂[(1 : ℝ), -Real.sqrt 2, 0]
noncomputable def r29 : V3 := !₂[(1 : ℝ), -Real.sqrt 2, 1]
noncomputable def r30 : V3 := !₂[(1 : ℝ), -Real.sqrt 2, (-1)]
noncomputable def r33 : V3 := !₂[(Real.sqrt 2 : ℝ), 0, 1]
noncomputable def r34 : V3 := !₂[(Real.sqrt 2 : ℝ), 0, (-1)]
noncomputable def r35 : V3 := !₂[(Real.sqrt 2 : ℝ), 1, 0]
noncomputable def r36 : V3 := !₂[(Real.sqrt 2 : ℝ), 1, 1]
noncomputable def r37 : V3 := !₂[(Real.sqrt 2 : ℝ), 1, (-1)]
noncomputable def r40 : V3 := !₂[(Real.sqrt 2 : ℝ), (-1), 0]
noncomputable def r41 : V3 := !₂[(Real.sqrt 2 : ℝ), (-1), 1]
noncomputable def r42 : V3 := !₂[(Real.sqrt 2 : ℝ), (-1), (-1)]

theorem c2_ne : c2 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c2] at h2
theorem c3_ne : c3 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c3] at h2
theorem c9_ne : c9 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c9] at h2
theorem c10_ne : c10 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c10] at h2
theorem c15_ne : c15 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c15] at h2
theorem c16_ne : c16 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c16] at h2
theorem c19_ne : c19 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c19] at h2
theorem c24_ne : c24 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c24] at h2
theorem c25_ne : c25 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c25] at h2
theorem c28_ne : c28 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c28] at h2
theorem c29_ne : c29 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c29] at h2
theorem c31_ne : c31 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c31] at h2
theorem c32_ne : c32 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c32] at h2
theorem c34_ne : c34 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c34] at h2
theorem c35_ne : c35 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c35] at h2
theorem c36_ne : c36 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c36] at h2
theorem c42_ne : c42 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c42] at h2
theorem c43_ne : c43 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c43] at h2
theorem c45_ne : c45 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c45] at h2
theorem c46_ne : c46 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c46] at h2
theorem c47_ne : c47 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 2
  simp [c47] at h2
theorem c52_ne : c52 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c52] at h2
theorem c54_ne : c54 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c54] at h2
theorem c56_ne : c56 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c56] at h2
theorem c57_ne : c57 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c57] at h2
theorem c59_ne : c59 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c59] at h2
theorem c60_ne : c60 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c60] at h2
theorem c62_ne : c62 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c62] at h2
theorem c64_ne : c64 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c64] at h2
theorem c66_ne : c66 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c66] at h2
theorem c67_ne : c67 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [c67] at h2
theorem c68_ne : c68 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c68] at h2
theorem c69_ne : c69 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [c69] at h2
theorem r0_ne : r0 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 2
  simp [r0] at h2
theorem r1_ne : r1 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r1] at h2
theorem r2_ne : r2 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r2] at h2
theorem r3_ne : r3 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r3] at h2
theorem r4_ne : r4 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r4] at h2
theorem r5_ne : r5 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r5] at h2
theorem r6_ne : r6 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 2
  simp [r6] at h2
theorem r7_ne : r7 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 2
  simp [r7] at h2
theorem r8_ne : r8 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r8] at h2
theorem r9_ne : r9 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r9] at h2
theorem r10_ne : r10 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r10] at h2
theorem r11_ne : r11 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r11] at h2
theorem r12_ne : r12 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r12] at h2
theorem r13_ne : r13 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r13] at h2
theorem r16_ne : r16 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r16] at h2
theorem r17_ne : r17 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r17] at h2
theorem r18_ne : r18 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r18] at h2
theorem r21_ne : r21 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r21] at h2
theorem r22_ne : r22 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r22] at h2
theorem r23_ne : r23 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r23] at h2
theorem r24_ne : r24 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r24] at h2
theorem r25_ne : r25 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r25] at h2
theorem r28_ne : r28 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r28] at h2
theorem r29_ne : r29 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r29] at h2
theorem r30_ne : r30 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 0
  simp [r30] at h2
theorem r33_ne : r33 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 2
  simp [r33] at h2
theorem r34_ne : r34 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 2
  simp [r34] at h2
theorem r35_ne : r35 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r35] at h2
theorem r36_ne : r36 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r36] at h2
theorem r37_ne : r37 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r37] at h2
theorem r40_ne : r40 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r40] at h2
theorem r41_ne : r41 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r41] at h2
theorem r42_ne : r42 ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg WithLp.ofLp h) 1
  simp [r42] at h2

/-! ### Boolean bookkeeping lemmas for an "exactly one" constraint -/

variable {x y z : Bool}

theorem tri_true0 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hx : x = true) : y = false ∧ z = false := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_true1 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hy : y = true) : x = false ∧ z = false := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_true2 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hz : z = true) : x = false ∧ y = false := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_ff01 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hx : x = false) (hy : y = false) : z = true := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_ff02 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hx : x = false) (hz : z = false) : y = true := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_ff12 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hy : y = false) (hz : z = false) : x = true := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_not2_01 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hx : x = true) (hy : y = true) : False := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_not2_02 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hx : x = true) (hz : z = true) : False := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_not2_12 (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hy : y = true) (hz : z = true) : False := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem tri_not_all (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hx : x = false) (hy : y = false) (hz : z = false) : False := by
  cases x <;> cases y <;> cases z <;> simp_all

end KS3

end Frontier

import RequestProject.KS3Vectors

/-!
# Kochen–Specker in dimension three

The case analysis refuting the existence of a `{0,1}`-valuation on `ℝ³`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Frontier
/--
**Kochen–Specker theorem in dimension three.**

There is no `{0,1}`-valued (noncontextual) assignment on the vectors of `ℝ³` assigning
the value `1` to exactly one vector of each orthogonal frame.  The proof exhibits a
33-ray configuration with coordinates in `{0, ±1, ±√2}` and refutes every valuation by
case analysis.
-/
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
theorem ne_zero_of_coord {v : KSSpace} (i : Fin 4) (h : v i ≠ 0) : v ≠ 0 := by
  intro hv
  apply h
  simp [hv]

/-! ### The 18 vectors of the Cabello–Estebaranz–García-Alcaine set -/

def u1 : KSSpace := !₂[(0:ℝ), 0, 0, 1]
def u2 : KSSpace := !₂[(0:ℝ), 0, 1, 0]
def u3 : KSSpace := !₂[(1:ℝ), 1, 0, 0]
def u4 : KSSpace := !₂[(1:ℝ), -1, 0, 0]
def u5 : KSSpace := !₂[(0:ℝ), 1, 0, 0]
def u6 : KSSpace := !₂[(1:ℝ), 0, 1, 0]
def u7 : KSSpace := !₂[(1:ℝ), 0, -1, 0]
def u8 : KSSpace := !₂[(1:ℝ), -1, 1, -1]
def u9 : KSSpace := !₂[(1:ℝ), -1, -1, 1]
def u10 : KSSpace := !₂[(0:ℝ), 0, 1, 1]
def u11 : KSSpace := !₂[(1:ℝ), 1, 1, 1]
def u12 : KSSpace := !₂[(0:ℝ), 1, 0, -1]
def u13 : KSSpace := !₂[(1:ℝ), 0, 0, 1]
def u14 : KSSpace := !₂[(1:ℝ), 0, 0, -1]
def u15 : KSSpace := !₂[(0:ℝ), 1, -1, 0]
def u16 : KSSpace := !₂[(1:ℝ), 1, -1, 1]
def u17 : KSSpace := !₂[(1:ℝ), 1, 1, -1]
def u18 : KSSpace := !₂[(-1:ℝ), 1, 1, 1]

end KS

/--
**Kochen–Specker theorem** (base case, dimension four).

There is no `{0,1}`-valued (noncontextual) assignment `f` on the vectors of a four dimensional
real Hilbert space with the property that in every orthogonal frame (four pairwise orthogonal
nonzero vectors) exactly one vector is assigned the value `1`.

The proof uses the 18-vector, 9-basis Kochen–Specker set of Cabello, Estebaranz and
García-Alcaine: each of the 18 vectors occurs in exactly two of the 9 bases, so summing the
nine "exactly one" constraints gives `9 = 2 * (number of vectors assigned 1)`, which is
impossible by parity.
-/
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
noncomputable def embed {m n : ℕ} (σ : Fin m → Fin n) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) := ∑ i, x i • EuclideanSpace.single (σ i) (1 : ℝ)

theorem embed_apply_of_notMem {m n : ℕ} (σ : Fin m → Fin n) (x : EuclideanSpace ℝ (Fin m))
    (j : Fin n) (hj : j ∉ Set.range σ) : (embed σ x) j = 0 := by
  have h : ∀ i, σ i ≠ j := fun i hi => hj ⟨i, hi⟩
  simp [embed, h]

theorem embed_inner {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (x y : EuclideanSpace ℝ (Fin m)) : inner ℝ (embed σ x) (embed σ y) = inner ℝ x y := by
  simp [embed, inner_sum, sum_inner, hσ.eq_iff, PiLp.inner_apply, mul_comm]

theorem embed_ne_zero {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ≠ 0) : embed σ x ≠ 0 := by
  intro h
  apply hx
  have h2 := embed_inner σ hσ x x
  rw [h] at h2
  simp at h2
  have hnorm : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hnorm

theorem exists_injection_apply_zero {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (k : Fin n) :
    ∃ σ : Fin m → Fin n, Function.Injective σ ∧ σ ⟨0, hm⟩ = k := by
  refine ⟨fun i => Equiv.swap k (Fin.castLE hmn ⟨0, hm⟩) (Fin.castLE hmn i), ?_, by simp⟩
  intro a b hab
  simpa using (Fin.castLE_injective hmn)
    ((Equiv.swap k (Fin.castLE hmn ⟨0, hm⟩)).injective hab)

end KS

/--
Reduction of the Kochen–Specker property from dimension `n` to a smaller dimension `m`.

If a valuation of the forbidden kind exists in dimension `n`, then one exists in every
dimension `m ≤ n` (with `0 < m`): in the standard orthogonal frame of `ℝⁿ` exactly one vector
`e k` is assigned `1`, and any `m`-dimensional coordinate subspace containing `e k` inherits
such a valuation.
-/
theorem kochen_specker_of_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hbase : ¬ ∃ g : EuclideanSpace ℝ (Fin m) → Bool,
        ∀ v : Fin m → EuclideanSpace ℝ (Fin m),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if g (v i) then (1 : ℕ) else 0) = 1) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → Bool,
        ∀ v : Fin n → EuclideanSpace ℝ (Fin n),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if f (v i) then (1 : ℕ) else 0) = 1 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rintro ⟨f, hf⟩
  have hsingle_ne : ∀ j : Fin n, (EuclideanSpace.single j (1 : ℝ)) ≠ 0 := by
    intro j h
    have := congrFun (congrArg WithLp.ofLp h) j
    simp at this
  -- In the standard frame exactly one vector is assigned `1`; call its index `k`.
  have hstd := hf (fun j => EuclideanSpace.single j (1 : ℝ)) (fun j => hsingle_ne j)
    (by
      intro i j hij
      simp [EuclideanSpace.inner_single_right, EuclideanSpace.single_apply, hij.symm])
  rw [Finset.sum_boole] at hstd
  obtain ⟨k, hkS⟩ := Finset.card_eq_one.mp (by exact_mod_cast hstd)
  have hk' : ∀ j : Fin n, j ≠ k → f (EuclideanSpace.single j (1 : ℝ)) = false := by
    intro j hj
    by_contra hcon
    have hjt : f (EuclideanSpace.single j (1 : ℝ)) = true := by
      cases h : f (EuclideanSpace.single j (1 : ℝ)) <;> simp_all
    have hmem : j ∈ Finset.univ.filter
        (fun j : Fin n => f (EuclideanSpace.single j (1 : ℝ)) = true) := by simp [hjt]
    rw [hkS] at hmem
    exact hj (by simpa using hmem)
  obtain ⟨σ, hσ, hσ0⟩ := KS.exists_injection_apply_zero hm hmn k
  -- Transport the valuation to the `m`-dimensional subspace spanned by the `e (σ i)`.
  refine hbase ⟨fun x => f (KS.embed σ x), ?_⟩
  intro v hv hvo
  set V : Fin n → EuclideanSpace ℝ (Fin n) := fun j =>
    if h : j ∈ Set.range σ then KS.embed σ (v (Function.invFun σ j))
    else EuclideanSpace.single j (1 : ℝ) with hV
  have hinv : ∀ i, Function.invFun σ (σ i) = i := Function.leftInverse_invFun hσ
  have hVσ : ∀ i, V (σ i) = KS.embed σ (v i) := by
    intro i
    simp only [hV, dif_pos (Set.mem_range_self i), hinv]
  have hVnot : ∀ j, j ∉ Set.range σ → V j = EuclideanSpace.single j (1 : ℝ) := by
    intro j hj; simp only [hV, dif_neg hj]
  have hVne : ∀ j, V j ≠ 0 := by
    intro j
    by_cases h : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := h
      rw [hVσ i]
      exact KS.embed_ne_zero σ hσ (hv i)
    · rw [hVnot j h]
      exact hsingle_ne j
  have hVo : ∀ j j', j ≠ j' → inner ℝ (V j) (V j') = (0 : ℝ) := by
    intro j j' hjj'
    by_cases h : j ∈ Set.range σ <;> by_cases h' : j' ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := h
      obtain ⟨i', rfl⟩ := h'
      rw [hVσ i, hVσ i', KS.embed_inner σ hσ]
      exact hvo i i' (fun hc => hjj' (by rw [hc]))
    · obtain ⟨i, rfl⟩ := h
      rw [hVσ i, hVnot j' h', EuclideanSpace.inner_single_right]
      simp [KS.embed_apply_of_notMem σ (v i) j' h']
    · obtain ⟨i', rfl⟩ := h'
      rw [hVσ i', hVnot j h, EuclideanSpace.inner_single_left]
      simp [KS.embed_apply_of_notMem σ (v i') j h]
    · rw [hVnot j h, hVnot j' h', EuclideanSpace.inner_single_right,
        EuclideanSpace.single_apply]
      simp [hjj'.symm]
  have key := hf V hVne hVo
  rw [show (∑ j, if f (V j) then (1 : ℕ) else 0)
      = ∑ j ∈ Finset.univ.image σ, (if f (V j) then (1 : ℕ) else 0) from ?_] at key
  · rw [Finset.sum_image (fun a _ b _ h => hσ h)] at key
    simpa [hVσ] using key
  · refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ hj
    have hj' : j ∉ Set.range σ := by
      rintro ⟨i, hi⟩
      exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    have hjk : j ≠ k := by
      rintro rfl
      exact hj' ⟨⟨0, hm⟩, hσ0⟩
    rw [hVnot j hj', hk' j hjk]
    simp

/--
**Kochen–Specker theorem.**

For every dimension `n ≥ 3` there is no noncontextual hidden-variable assignment for quantum
mechanics in dimension `n`: no `{0,1}`-valued function `f` on the vectors of the `n`-dimensional
real Hilbert space assigns the value `1` to exactly one vector of each orthogonal frame
(`n` pairwise orthogonal nonzero vectors).

The three dimensional case `Frontier.kochen_specker_dim_three` is proved from an explicit
33-ray configuration, and the general case follows by restricting a hypothetical valuation to a
three dimensional coordinate subspace.
-/
theorem kochen_specker (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → Bool,
        ∀ v : Fin n → EuclideanSpace ℝ (Fin n),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if f (v i) then (1 : ℕ) else 0) = 1 :=
  kochen_specker_of_le (by norm_num) hn kochen_specker_dim_three

/-- The Kochen–Specker theorem in every dimension `n ≥ 4`, deduced from the four dimensional
base case `Frontier.kochen_specker_dim_four`. -/
theorem kochen_specker_of_four_le (n : ℕ) (hn : 4 ≤ n) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → Bool,
        ∀ v : Fin n → EuclideanSpace ℝ (Fin n),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if f (v i) then (1 : ℕ) else 0) = 1 :=
  kochen_specker_of_le (by norm_num) hn kochen_specker_dim_four

end Frontier

