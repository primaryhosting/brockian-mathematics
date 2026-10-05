import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/
noncomputable def cycAngle (m : ℕ) : ℝ := 2 * Real.pi / (m + 3)

/-- The primitive `n`-th root of unity for `n = m + 3`. -/
noncomputable def cycRoot (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / ((m + 3 : ℕ) : ℂ))

section
variable {m : ℕ}

lemma cycAngle_pos : 0 < cycAngle m := by
  unfold cycAngle
  have := Real.pi_pos
  positivity

lemma cycAngle_mul : ((m : ℝ) + 3) * cycAngle m = 2 * Real.pi := by
  unfold cycAngle
  have h : ((m : ℝ) + 3) ≠ 0 := by positivity
  field_simp

lemma cycAngle_le_pi : cycAngle m ≤ Real.pi := by
  unfold cycAngle
  rw [div_le_iff₀ (by positivity)]
  have := Real.pi_pos
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma cos_cycAngle_mod (a : ℕ) :
    Real.cos ((a % (m + 3) : ℕ) * cycAngle m) = Real.cos (a * cycAngle m) := by
  have key : (a : ℝ) * cycAngle m
      = ((a % (m + 3) : ℕ) : ℝ) * cycAngle m + ((a / (m + 3) : ℕ) : ℝ) * (2 * Real.pi) := by
    have h := Nat.mod_add_div a (m + 3)
    have hc : ((a % (m + 3) : ℕ) : ℝ) + ((m : ℝ) + 3) * ((a / (m + 3) : ℕ) : ℝ) = a := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
    rw [← hc, ← cycAngle_mul (m := m)]
    ring
  rw [key, Real.cos_add_nat_mul_two_pi]

/-- The action of the Laplacian of the cycle graph on a vector. -/
lemma lapMatrix_cycle_mulVec (R : Type*) [NonAssocRing R] (x : Fin (m + 3) → R)
    (v : Fin (m + 3)) :
    ((cycleGraph (m + 3)).lapMatrix R *ᵥ x) v = 2 * x v - x (v - 1) - x (v + 1) := by
  have hne : v - 1 ≠ v + 1 := by
    intro h
    have h2 : ({v - 1, v + 1} : Finset (Fin (m + 3))).card = 2 := by
      rw [← cycleGraph_neighborFinset]
      exact cycleGraph_degree_three_le
    rw [h] at h2
    simp at h2
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair hne]
  push_cast
  rw [sub_sub]

lemma fin_val_add_one (v : Fin (m + 3)) : (v + 1).val = (v.val + 1) % (m + 3) := by
  rw [Fin.val_add]
  norm_num [Nat.mod_eq_of_lt]

lemma fin_val_sub_one (v : Fin (m + 3)) : (v - 1).val = (v.val + (m + 2)) % (m + 3) := by
  simp [Fin.sub_def, Nat.add_comm]

lemma cycRoot_isPrimitiveRoot : IsPrimitiveRoot (cycRoot m) (m + 3) :=
  Complex.isPrimitiveRoot_exp (m + 3) (by omega)

lemma cycRoot_pow_congr {a b : ℕ} (h : a ≡ b [MOD m + 3]) :
    cycRoot m ^ a = cycRoot m ^ b := by
  have hp : cycRoot m ^ (m + 3) = 1 := cycRoot_isPrimitiveRoot.pow_eq_one
  have key : ∀ c : ℕ, cycRoot m ^ c = cycRoot m ^ (c % (m + 3)) := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c (m + 3)]
    rw [pow_add, pow_mul, hp, one_pow, mul_one]
  rw [key a, key b, h]

lemma cycRoot_pow_eq (k : ℕ) :
    cycRoot m ^ k = Complex.exp ((k * cycAngle m : ℝ) * Complex.I) := by
  unfold cycRoot cycAngle
  rw [← Complex.exp_nat_mul]
  congr 1
  have h : ((m + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

lemma cycRoot_pow_re (k : ℕ) : (cycRoot m ^ k).re = Real.cos (k * cycAngle m) := by
  rw [cycRoot_pow_eq, Complex.exp_ofReal_mul_I_re]

lemma cycRoot_quad (k : ℕ) :
    (cycRoot m ^ k) ^ 2 + 1 = ((2 * Real.cos (k * cycAngle m) : ℝ) : ℂ) * cycRoot m ^ k := by
  rw [cycRoot_pow_eq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  have h : (Real.cos ((k : ℝ) * cycAngle m) : ℂ) ^ 2
      + (Real.sin ((k : ℝ) * cycAngle m) : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.cos_sq_add_sin_sq ((k : ℝ) * cycAngle m))
  linear_combination -h + (Real.sin ((k : ℝ) * cycAngle m) : ℂ) ^ 2 * Complex.I_sq

lemma sum_cos_cycAngle : ∑ v : Fin (m + 3), Real.cos (v.val * cycAngle m) = 0 := by
  have h : ∑ v : Fin (m + 3), cycRoot m ^ v.val = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => cycRoot m ^ i)]
    exact cycRoot_isPrimitiveRoot.geom_sum_eq_zero (by omega)
  calc ∑ v : Fin (m + 3), Real.cos (v.val * cycAngle m)
      = ∑ v : Fin (m + 3), (cycRoot m ^ v.val).re := by simp [cycRoot_pow_re]
    _ = (∑ v : Fin (m + 3), cycRoot m ^ v.val).re := by rw [Complex.re_sum]
    _ = 0 := by rw [h]; simp

/-- The eigenvector realizing the Fiedler value. -/
noncomputable def fiedlerVec (m : ℕ) : Fin (m + 3) → ℝ := fun v => Real.cos (v.val * cycAngle m)

lemma fiedlerVec_ne_zero : fiedlerVec m ≠ 0 := by
  intro h
  have h0 : fiedlerVec m 0 = 0 := by rw [h]; rfl
  simp [fiedlerVec] at h0

lemma sum_fiedlerVec : ∑ v : Fin (m + 3), fiedlerVec m v = 0 := sum_cos_cycAngle

lemma lapMatrix_mulVec_fiedlerVec :
    (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ fiedlerVec m
      = (2 - 2 * Real.cos (cycAngle m)) • fiedlerVec m := by
  funext v
  rw [lapMatrix_cycle_mulVec]
  simp only [fiedlerVec, Pi.smul_apply, smul_eq_mul, fin_val_add_one, fin_val_sub_one,
    cos_cycAngle_mod]
  have e1 : ((v.val + (m + 2) : ℕ) : ℝ) * cycAngle m
      = ((v.val : ℝ) * cycAngle m - cycAngle m) + 2 * Real.pi := by
    push_cast
    linear_combination cycAngle_mul (m := m)
  have e2 : ((v.val + 1 : ℕ) : ℝ) * cycAngle m = (v.val : ℝ) * cycAngle m + cycAngle m := by
    push_cast; ring
  rw [e1, e2, Real.cos_add_two_pi, Real.cos_sub, Real.cos_add]
  ring

/-- The (complex) Fourier matrix of the cycle. -/
noncomputable def fourierMat (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ :=
  fun j k => cycRoot m ^ (j.val * k.val)

/-- The eigenvalues of the cycle Laplacian. -/
noncomputable def cycEigen (m : ℕ) (k : Fin (m + 3)) : ℝ := 2 - 2 * Real.cos (k.val * cycAngle m)

lemma lapMatrix_mul_fourierMat :
    (cycleGraph (m + 3)).lapMatrix ℂ * fourierMat m
      = fourierMat m * Matrix.diagonal (fun k => ((cycEigen m k : ℝ) : ℂ)) := by
  ext j k
  have hL : ((cycleGraph (m + 3)).lapMatrix ℂ * fourierMat m) j k
      = ((cycleGraph (m + 3)).lapMatrix ℂ *ᵥ (fun i => fourierMat m i k)) j := rfl
  rw [hL, lapMatrix_cycle_mulVec, Matrix.mul_diagonal]
  set b := j.val with hb
  set c := k.val with hc
  simp only [fourierMat, fin_val_add_one, fin_val_sub_one]
  have hmod1 : cycRoot m ^ (((b + (m + 2)) % (m + 3)) * c) = cycRoot m ^ ((b + (m + 2)) * c) :=
    cycRoot_pow_congr (Nat.ModEq.mul_right c (Nat.mod_modEq _ _))
  have hmod2 : cycRoot m ^ (((b + 1) % (m + 3)) * c) = cycRoot m ^ ((b + 1) * c) :=
    cycRoot_pow_congr (Nat.ModEq.mul_right c (Nat.mod_modEq _ _))
  rw [hmod1, hmod2]
  have hu : cycRoot m ^ ((b + (m + 2)) * c) * cycRoot m ^ c = cycRoot m ^ (b * c) := by
    rw [← pow_add]
    apply cycRoot_pow_congr
    have hrw : (b + (m + 2)) * c + c = b * c + (m + 3) * c := by ring
    rw [hrw]
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  have hsplit : cycRoot m ^ ((b + 1) * c) = cycRoot m ^ (b * c) * cycRoot m ^ c := by
    rw [← pow_add]
    congr 1
    ring
  rw [hsplit]
  have hq := cycRoot_quad (m := m) c
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat] at hq
  simp only [cycEigen, ← hc, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (cycRoot m ^ c - 2 * (Real.cos ((c : ℝ) * cycAngle m) : ℂ)) * hu
    - (cycRoot m ^ ((b + (m + 2)) * c)) * hq

lemma det_fourierMat_ne_zero : (fourierMat m).det ≠ 0 := by
  have hv : fourierMat m = (Matrix.vandermonde (fun k : Fin (m + 3) => cycRoot m ^ k.val))ᵀ := by
    ext j k
    simp [fourierMat, Matrix.vandermonde, Matrix.transpose_apply, ← pow_mul, mul_comm]
  rw [hv, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr
    (fun a b h => Fin.ext (cycRoot_isPrimitiveRoot.pow_inj a.isLt b.isLt h))

lemma lapMatrix_map_ofReal :
    ((cycleGraph (m + 3)).lapMatrix ℝ).map (fun r : ℝ => (r : ℂ))
      = (cycleGraph (m + 3)).lapMatrix ℂ := by
  ext i j
  simp [Matrix.map_apply, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

lemma eigenvalue_eq (μ : ℝ) (x : Fin (m + 3) → ℝ) (hx : x ≠ 0)
    (heig : (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x = μ • x) :
    ∃ k : Fin (m + 3), μ = cycEigen m k := by
  classical
  set M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
    (cycleGraph (m + 3)).lapMatrix ℝ - Matrix.diagonal (fun _ => μ) with hM
  have hMx : M *ᵥ x = 0 := by
    funext i
    have hi := congrFun heig i
    simp [hM, Matrix.sub_mulVec, hi]
  have hdet : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hMx⟩
  set Mc : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ :=
    (cycleGraph (m + 3)).lapMatrix ℂ - Matrix.diagonal (fun _ => (μ : ℂ)) with hMc
  have hmap : Mc = M.map Complex.ofRealHom := by
    have hentry : ∀ i j, (((cycleGraph (m + 3)).lapMatrix ℝ i j : ℝ) : ℂ)
        = (cycleGraph (m + 3)).lapMatrix ℂ i j := by
      intro i j
      have h := congrFun (congrFun (lapMatrix_map_ofReal (m := m)) i) j
      simpa [Matrix.map_apply] using h
    ext i j
    simp [hMc, hM, Matrix.map_apply, Matrix.sub_apply, Matrix.diagonal_apply, ← hentry]
    split_ifs <;> simp
  have hdetC : Mc.det = 0 := by
    have hd := RingHom.map_det Complex.ofRealHom M
    simp [RingHom.mapMatrix_apply] at hd
    rw [hmap, ← hd, hdet]
    simp
  have hprod : Mc * fourierMat m
      = fourierMat m * Matrix.diagonal (fun k => ((cycEigen m k : ℝ) : ℂ) - (μ : ℂ)) := by
    rw [hMc, Matrix.sub_mul, lapMatrix_mul_fourierMat]
    ext j k
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply]
    ring
  have hdet2 : Mc.det * (fourierMat m).det
      = (fourierMat m).det * ∏ k : Fin (m + 3), (((cycEigen m k : ℝ) : ℂ) - (μ : ℂ)) := by
    rw [← Matrix.det_mul, hprod, Matrix.det_mul, Matrix.det_diagonal]
  rw [hdetC, zero_mul] at hdet2
  have hz : ∏ k : Fin (m + 3), (((cycEigen m k : ℝ) : ℂ) - (μ : ℂ)) = 0 := by
    rcases mul_eq_zero.mp hdet2.symm with h | h
    · exact absurd h det_fourierMat_ne_zero
    · exact h
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hz
  refine ⟨k, ?_⟩
  have hkc : ((cycEigen m k : ℝ) : ℂ) = (μ : ℂ) := by linear_combination hk
  exact_mod_cast hkc.symm

lemma cos_le_cos_cycAngle {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < m + 3) :
    Real.cos (k * cycAngle m) ≤ Real.cos (cycAngle m) := by
  have hpos : 0 < cycAngle m := cycAngle_pos
  have hmul : ((m : ℝ) + 3) * cycAngle m = 2 * Real.pi := cycAngle_mul
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : (k : ℝ) + 1 ≤ (m : ℝ) + 3 := by exact_mod_cast hk2
  have hlow : cycAngle m ≤ (k : ℝ) * cycAngle m := by nlinarith
  have hhigh : (k : ℝ) * cycAngle m ≤ 2 * Real.pi - cycAngle m := by nlinarith
  rcases le_or_gt ((k : ℝ) * cycAngle m) Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hpos.le h hlow
  · rw [← Real.cos_two_pi_sub ((k : ℝ) * cycAngle m)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith) (by linarith)

end

/-- **Fiedler value of the cycle graph.**  For `n ≥ 3`, the algebraic connectivity of the
cycle graph `C_n`, i.e. the smallest eigenvalue of its Laplacian matrix admitting an
eigenvector orthogonal to the all-ones vector (equivalently, the second-smallest Laplacian
eigenvalue, since `C_n` is connected), equals `2 - 2 cos (2π/n)`. -/
theorem cycle_fiedler_value (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {μ : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (∑ i, x i = 0) ∧
        (SimpleGraph.cycleGraph n).lapMatrix ℝ *ᵥ x = μ • x}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  have hang : 2 * Real.pi / ((m + 3 : ℕ) : ℝ) = cycAngle m := by
    unfold cycAngle
    push_cast
    ring
  rw [hang]
  constructor
  · exact ⟨fiedlerVec m, fiedlerVec_ne_zero, sum_fiedlerVec, lapMatrix_mulVec_fiedlerVec⟩
  · rintro μ ⟨x, hx, hsum, heig⟩
    obtain ⟨k, hk⟩ := eigenvalue_eq μ x hx heig
    rcases Nat.eq_zero_or_pos k.val with hk0 | hk0
    · exfalso
      have hμ : μ = 0 := by
        rw [hk]
        simp [cycEigen, hk0]
      have hzero : (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x = 0 := by
        rw [heig, hμ]
        simp
      have hconst : ∀ i : Fin (m + 3), x i = x 0 := by
        intro i
        exact (lapMatrix_mulVec_eq_zero_iff_forall_reachable _).mp hzero i 0
          (cycleGraph_connected.preconnected i 0)
      have hs : ((m : ℝ) + 3) * x 0 = 0 := by
        rw [← hsum]
        rw [Finset.sum_congr rfl (fun i _ => hconst i)]
        simp
      have hx0 : x 0 = 0 :=
        (mul_eq_zero.mp hs).resolve_left (by positivity)
      exact hx (funext fun i => by rw [hconst i, hx0]; rfl)
    · rw [hk, cycEigen]
      have := cos_le_cos_cycAngle (m := m) hk0 k.isLt
      linarith

end Frontier.Spectral
