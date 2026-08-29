import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

namespace Brockian

/-- The planar rotation matrix by an angle `t`. -/
noncomputable def rot (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

/-- The reflection of the plane fixing the first axis. -/
def refl : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

lemma rot_zero : rot 0 = 1 := by
  simp [rot, Matrix.one_fin_two]

lemma rot_mul (a b : ℝ) : rot a * rot b = rot (a + b) := by
  simp only [rot, Matrix.mul_fin_two, Real.cos_add, Real.sin_add]
  congr 1
  ring_nf

lemma refl_mul_refl : refl * refl = 1 := by
  simp [refl, Matrix.one_fin_two]

lemma refl_mul_rot (t : ℝ) : refl * rot t = rot (-t) * refl := by
  simp [refl, rot]

lemma rot_add_two_pi_mul (t : ℝ) (k : ℕ) : rot (t + k * (2 * Real.pi)) = rot t := by
  simp only [rot]
  rw [show ((k : ℝ)) = ((k : ℤ) : ℝ) by push_cast; ring, Real.cos_add_int_mul_two_pi,
    Real.sin_add_int_mul_two_pi]

/-- The angle attached to the vertex `i` of the regular `n`-gon. -/
noncomputable def ang (n : ℕ) (i : ZMod n) : ℝ := 2 * Real.pi * (i.val : ℝ) / (n : ℝ)

lemma rot_ang_mul (n : ℕ) (i j : ZMod n) :
    rot (ang n i) * rot (ang n j) = rot (ang n (i + j)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [ang, rot_zero]
  · haveI : NeZero n := ⟨by omega⟩
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have key : ang n i + ang n j = ang n (i + j) + ((i.val + j.val) / n : ℕ) * (2 * Real.pi) := by
      have hd : (n : ℝ) * (((i.val + j.val) / n : ℕ) : ℝ) + (((i.val + j.val) % n : ℕ) : ℝ)
          = ((i.val : ℝ) + (j.val : ℝ)) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.div_add_mod (i.val + j.val) n)
      simp only [ang, ZMod.val_add]
      field_simp
      nlinarith [hd, Real.pi_pos]
    rw [rot_mul, key, rot_add_two_pi_mul]

lemma ang_zero (n : ℕ) : ang n (0 : ZMod n) = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [ang]
  · haveI : NeZero n := ⟨by omega⟩
    simp [ang]

lemma rot_ang_zero (n : ℕ) : rot (ang n (0 : ZMod n)) = 1 := by
  rw [ang_zero, rot_zero]

lemma rot_neg_ang (n : ℕ) (i : ZMod n) : rot (-(ang n i)) = rot (ang n (-i)) := by
  have h1 : rot (ang n i) * rot (ang n (-i)) = 1 := by
    rw [rot_ang_mul]
    simpa using rot_ang_zero n
  have h2 : rot (-(ang n i)) * rot (ang n i) = 1 := by
    rw [rot_mul]
    simpa using rot_zero
  calc rot (-(ang n i)) = rot (-(ang n i)) * (rot (ang n i) * rot (ang n (-i))) := by
        rw [h1, mul_one]
    _ = (rot (-(ang n i)) * rot (ang n i)) * rot (ang n (-i)) := by rw [mul_assoc]
    _ = rot (ang n (-i)) := by rw [h2, one_mul]

lemma rot_ang_mul_refl (n : ℕ) (i : ZMod n) :
    rot (ang n i) * refl = refl * rot (ang n (-i)) := by
  rw [refl_mul_rot, rot_neg_ang, neg_neg]

/-- The standard two-dimensional real representation of the dihedral group of the regular
`n`-gon: `r i` acts as the rotation by `2πi/n` and `sr i` as a reflection. -/
noncomputable def dihedralRep (n : ℕ) : DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℝ where
  toFun g := match g with
    | DihedralGroup.r i => rot (ang n i)
    | DihedralGroup.sr i => refl * rot (ang n i)
  map_one' := by simpa using rot_ang_zero n
  map_mul' := by
    rintro (i | i) (j | j)
    · simpa [DihedralGroup.r_mul_r] using (rot_ang_mul n i j).symm
    · show refl * rot (ang n (j - i)) = rot (ang n i) * (refl * rot (ang n j))
      rw [← mul_assoc, rot_ang_mul_refl, mul_assoc, rot_ang_mul, sub_eq_neg_add]
    · show refl * rot (ang n (i + j)) = refl * rot (ang n i) * rot (ang n j)
      rw [mul_assoc, rot_ang_mul]
    · show rot (ang n (j - i)) = refl * rot (ang n i) * (refl * rot (ang n j))
      rw [mul_assoc, ← mul_assoc (rot (ang n i)) refl, rot_ang_mul_refl, ← mul_assoc,
        ← mul_assoc, refl_mul_refl, one_mul, rot_ang_mul, sub_eq_neg_add]

@[simp] lemma dihedralRep_r (n : ℕ) (i : ZMod n) :
    dihedralRep n (DihedralGroup.r i) = rot (ang n i) := rfl

@[simp] lemma dihedralRep_sr (n : ℕ) (i : ZMod n) :
    dihedralRep n (DihedralGroup.sr i) = refl * rot (ang n i) := rfl

lemma sin_ang_one_ne_zero {n : ℕ} (hn : 3 ≤ n) : Real.sin (ang n (1 : ZMod n)) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hval : ang n (1 : ZMod n) = 2 * Real.pi / (n : ℝ) := by
    simp [ang, ZMod.val_one]
  have hpos : 0 < ang n (1 : ZMod n) := by
    rw [hval]
    positivity
  have hlt : ang n (1 : ZMod n) < Real.pi := by
    rw [hval, div_lt_iff₀ hn0]
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

/-- **Equivariance for the standard representation of the regular `n`-gon** (`n ≥ 3`).
A real `2 × 2` matrix commutes with the whole standard representation of the dihedral
symmetry group of the regular `n`-gon if and only if it is a scalar matrix.  For `n = 5`
this is the pentagon (`D₅`) case. -/
theorem PentagonPentagonEquivarianceGeneral {n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ g : DihedralGroup n, M * dihedralRep n g = dihedralRep n g * M) ↔
      ∃ c : ℝ, M = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · intro hM
    -- commuting with the reflection forces the off-diagonal entries to vanish
    have h1 : M * refl = refl * M := by
      have := hM (DihedralGroup.sr 0)
      rwa [dihedralRep_sr, rot_ang_zero, mul_one] at this
    have h2 : M * rot (ang n 1) = rot (ang n 1) * M := hM (DihedralGroup.r 1)
    rw [Matrix.eta_fin_two M] at h1 h2
    simp only [refl, rot, Matrix.mul_fin_two] at h1 h2
    have e01 : M 0 1 = 0 := by
      have := congrFun (congrFun h1 0) 1
      simp at this
      linarith
    have e10 : M 1 0 = 0 := by
      have := congrFun (congrFun h1 1) 0
      simp at this
      linarith
    have e00 : M 0 0 = M 1 1 := by
      have h := congrFun (congrFun h2 1) 0
      simp [e01, e10] at h
      have hs := sin_ang_one_ne_zero hn
      have hmul : Real.sin (ang n 1) * M 0 0 = Real.sin (ang n 1) * M 1 1 := by
        linear_combination -h
      exact mul_left_cancel₀ hs hmul
    refine ⟨M 0 0, ?_⟩
    rw [Matrix.eta_fin_two M, e01, e10, e00]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two]
  · rintro ⟨c, rfl⟩ g
    simp

/-- The pentagon case: equivariance for the standard `D₅`-representation. -/
theorem pentagon_equivariance (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ g : DihedralGroup 5, M * dihedralRep 5 g = dihedralRep 5 g * M) ↔
      ∃ c : ℝ, M = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  PentagonPentagonEquivarianceGeneral (by norm_num) M

end Brockian

