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

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/
noncomputable def C8adj : Matrix (Fin 8) (Fin 8) ℝ := (SimpleGraph.cycleGraph 8).adjMatrix ℝ

/-- Multiplying the adjacency matrix of `C₈` by a vector adds the two cyclic neighbours. -/
lemma adj8_mulVec {α : Type*} [NonAssocSemiring α] (v : Fin 8 → α) (i : Fin 8) :
    ((SimpleGraph.cycleGraph 8).adjMatrix α *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset (n := 6),
    Finset.sum_pair]
  revert i; decide

lemma C8adj_mulVec (v : Fin 8 → ℝ) (i : Fin 8) : (C8adj *ᵥ v) i = v (i - 1) + v (i + 1) :=
  adj8_mulVec v i

lemma C8adj_mulVec_cons (a0 a1 a2 a3 a4 a5 a6 a7 : ℝ) :
    C8adj *ᵥ ![a0, a1, a2, a3, a4, a5, a6, a7] =
      ![a7 + a1, a0 + a2, a1 + a3, a2 + a4, a3 + a5, a4 + a6, a5 + a7, a6 + a0] := by
  funext i
  rw [C8adj_mulVec]
  fin_cases i <;> rfl

/-! ### The five distinct eigenvalues, with explicit eigenvectors -/

lemma vec_ne_zero_of_head {a0 a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : a0 ≠ 0) :
    ![a0, a1, a2, a3, a4, a5, a6, a7] ≠ 0 := by
  intro hc
  exact h (by simpa using congrFun hc 0)

lemma sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  positivity

lemma sqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma eigen_two : ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = (2 : ℝ) • v := by
  refine ⟨![1, 1, 1, 1, 1, 1, 1, 1], vec_ne_zero_of_head one_ne_zero, ?_⟩
  rw [C8adj_mulVec_cons]
  funext i; fin_cases i <;> norm_num

lemma eigen_neg_two : ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = (-2 : ℝ) • v := by
  refine ⟨![1, -1, 1, -1, 1, -1, 1, -1], vec_ne_zero_of_head one_ne_zero, ?_⟩
  rw [C8adj_mulVec_cons]
  funext i; fin_cases i <;> norm_num

lemma eigen_zero : ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = (0 : ℝ) • v := by
  refine ⟨![1, 0, -1, 0, 1, 0, -1, 0], vec_ne_zero_of_head one_ne_zero, ?_⟩
  rw [C8adj_mulVec_cons]
  funext i; fin_cases i <;> norm_num

lemma eigen_sqrt_two :
    ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = (Real.sqrt 2) • v := by
  refine ⟨![Real.sqrt 2, 1, 0, -1, -Real.sqrt 2, -1, 0, 1],
    vec_ne_zero_of_head sqrt_two_ne_zero, ?_⟩
  rw [C8adj_mulVec_cons]
  funext i
  have h2 := sqrt_two_sq
  fin_cases i <;> simp <;> nlinarith [h2]

lemma eigen_neg_sqrt_two :
    ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = (-Real.sqrt 2) • v := by
  refine ⟨![Real.sqrt 2, -1, 0, 1, -Real.sqrt 2, 1, 0, -1],
    vec_ne_zero_of_head sqrt_two_ne_zero, ?_⟩
  rw [C8adj_mulVec_cons]
  funext i
  have h2 := sqrt_two_sq
  fin_cases i <;> simp <;> nlinarith [h2]

/-! ### The values `2 cos (2πk/8)` -/

lemma cos_val_0 : 2 * Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / 8) = 2 := by norm_num

lemma cos_val_1 : 2 * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 8) = Real.sqrt 2 := by
  rw [show 2 * Real.pi * ((1 : ℕ) : ℝ) / 8 = Real.pi / 4 by push_cast; ring,
    Real.cos_pi_div_four]
  ring

lemma cos_val_2 : 2 * Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 8) = 0 := by
  rw [show 2 * Real.pi * ((2 : ℕ) : ℝ) / 8 = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two]
  ring

lemma cos_val_3 : 2 * Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) / 8) = -Real.sqrt 2 := by
  rw [show 2 * Real.pi * ((3 : ℕ) : ℝ) / 8 = Real.pi - Real.pi / 4 by push_cast; ring,
    Real.cos_pi_sub, Real.cos_pi_div_four]
  ring

lemma cos_val_4 : 2 * Real.cos (2 * Real.pi * ((4 : ℕ) : ℝ) / 8) = -2 := by
  rw [show 2 * Real.pi * ((4 : ℕ) : ℝ) / 8 = Real.pi by push_cast; ring, Real.cos_pi]
  ring

lemma cos_val_5 : 2 * Real.cos (2 * Real.pi * ((5 : ℕ) : ℝ) / 8) = -Real.sqrt 2 := by
  rw [show 2 * Real.pi * ((5 : ℕ) : ℝ) / 8 = Real.pi + Real.pi / 4 by push_cast; ring,
    Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
  ring

lemma cos_val_6 : 2 * Real.cos (2 * Real.pi * ((6 : ℕ) : ℝ) / 8) = 0 := by
  rw [show 2 * Real.pi * ((6 : ℕ) : ℝ) / 8 = Real.pi + Real.pi / 2 by push_cast; ring,
    Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

lemma cos_val_7 : 2 * Real.cos (2 * Real.pi * ((7 : ℕ) : ℝ) / 8) = Real.sqrt 2 := by
  rw [show 2 * Real.pi * ((7 : ℕ) : ℝ) / 8 = 2 * Real.pi - Real.pi / 4 by push_cast; ring,
    Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_four]
  ring

/-! ### Every eigenvalue is a root of `X⁵ - 6X³ + 8X` -/

/-- If the eight numbers `c₀,…,c₇` satisfy the cyclic three-term recurrence with parameter `m`
and are not all zero, then `m` is a root of `X⁵ - 6X³ + 8X = X(X²-2)(X²-4)`. -/
lemma quintic_root_of_cyclic_relation (m c0 c1 c2 c3 c4 c5 c6 c7 : ℝ)
    (h0 : c7 + c1 = m * c0) (h1 : c0 + c2 = m * c1) (h2 : c1 + c3 = m * c2)
    (h3 : c2 + c4 = m * c3) (h4 : c3 + c5 = m * c4) (h5 : c4 + c6 = m * c5)
    (h6 : c5 + c7 = m * c6) (h7 : c6 + c0 = m * c7)
    (hne : ¬ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0)) :
    m ^ 5 - 6 * m ^ 3 + 8 * m = 0 := by
  have q0 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c0 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h0 + (-(m ^ 3 - 3 * m)) * h1 +
      (-(m ^ 3 - 3 * m)) * h7 + (-(m ^ 2 - 2)) * h2 + (-(m ^ 2 - 2)) * h6 + (-m) * h3 +
      (-m) * h5 + (-2 : ℝ) * h4
  have q1 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c1 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h1 + (-(m ^ 3 - 3 * m)) * h2 +
      (-(m ^ 3 - 3 * m)) * h0 + (-(m ^ 2 - 2)) * h3 + (-(m ^ 2 - 2)) * h7 + (-m) * h4 +
      (-m) * h6 + (-2 : ℝ) * h5
  have q2 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c2 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h2 + (-(m ^ 3 - 3 * m)) * h3 +
      (-(m ^ 3 - 3 * m)) * h1 + (-(m ^ 2 - 2)) * h4 + (-(m ^ 2 - 2)) * h0 + (-m) * h5 +
      (-m) * h7 + (-2 : ℝ) * h6
  have q3 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c3 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h3 + (-(m ^ 3 - 3 * m)) * h4 +
      (-(m ^ 3 - 3 * m)) * h2 + (-(m ^ 2 - 2)) * h5 + (-(m ^ 2 - 2)) * h1 + (-m) * h6 +
      (-m) * h0 + (-2 : ℝ) * h7
  have q4 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c4 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h4 + (-(m ^ 3 - 3 * m)) * h5 +
      (-(m ^ 3 - 3 * m)) * h3 + (-(m ^ 2 - 2)) * h6 + (-(m ^ 2 - 2)) * h2 + (-m) * h7 +
      (-m) * h1 + (-2 : ℝ) * h0
  have q5 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c5 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h5 + (-(m ^ 3 - 3 * m)) * h6 +
      (-(m ^ 3 - 3 * m)) * h4 + (-(m ^ 2 - 2)) * h7 + (-(m ^ 2 - 2)) * h3 + (-m) * h0 +
      (-m) * h2 + (-2 : ℝ) * h1
  have q6 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c6 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h6 + (-(m ^ 3 - 3 * m)) * h7 +
      (-(m ^ 3 - 3 * m)) * h5 + (-(m ^ 2 - 2)) * h0 + (-(m ^ 2 - 2)) * h4 + (-m) * h1 +
      (-m) * h3 + (-2 : ℝ) * h2
  have q7 : (m ^ 5 - 6 * m ^ 3 + 8 * m) * c7 = 0 := by
    linear_combination (-(m ^ 4 - 4 * m ^ 2 + 2)) * h7 + (-(m ^ 3 - 3 * m)) * h0 +
      (-(m ^ 3 - 3 * m)) * h6 + (-(m ^ 2 - 2)) * h1 + (-(m ^ 2 - 2)) * h5 + (-m) * h2 +
      (-m) * h4 + (-2 : ℝ) * h3
  push_neg at hne
  by_contra hm
  refine hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    [exact (mul_eq_zero.1 q0).resolve_left hm;
     exact (mul_eq_zero.1 q1).resolve_left hm;
     exact (mul_eq_zero.1 q2).resolve_left hm;
     exact (mul_eq_zero.1 q3).resolve_left hm;
     exact (mul_eq_zero.1 q4).resolve_left hm;
     exact (mul_eq_zero.1 q5).resolve_left hm;
     exact (mul_eq_zero.1 q6).resolve_left hm;
     exact (mul_eq_zero.1 q7).resolve_left hm]

/-- **Hückel theory for cyclic C₈ (cyclooctatetraene).**  A real number `μ` is an eigenvalue of
the adjacency matrix of the cycle graph `C₈` if and only if `μ = 2 cos (2πk/8)` for some
`k ∈ {0, 1, …, 7}`. -/
theorem huckel_C8 (μ : ℝ) :
    (∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 8 ∧ μ = 2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have h : ∀ i : Fin 8, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      rw [← C8adj_mulVec, hv]
      rfl
    have hne : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0 ∧
        v 7 = 0) := by
      rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
      refine hv0 (funext fun i => ?_)
      fin_cases i
      · exact a0
      · exact a1
      · exact a2
      · exact a3
      · exact a4
      · exact a5
      · exact a6
      · exact a7
    have hroot : μ ^ 5 - 6 * μ ^ 3 + 8 * μ = 0 :=
      quintic_root_of_cyclic_relation μ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
        (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) hne
    have hfac : μ * ((μ ^ 2 - 2) * (μ ^ 2 - 4)) = 0 := by linarith [hroot, sq_nonneg μ]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := sqrt_two_sq
    rcases mul_eq_zero.1 hfac with hμ | hrest
    · exact ⟨2, by norm_num, by rw [cos_val_2, hμ]⟩
    rcases mul_eq_zero.1 hrest with hμ | hμ
    · have : (μ - Real.sqrt 2) * (μ + Real.sqrt 2) = 0 := by nlinarith [hμ, h2]
      rcases mul_eq_zero.1 this with h' | h'
      · exact ⟨1, by norm_num, by rw [cos_val_1]; linarith⟩
      · exact ⟨3, by norm_num, by rw [cos_val_3]; linarith⟩
    · have : (μ - 2) * (μ + 2) = 0 := by nlinarith [hμ]
      rcases mul_eq_zero.1 this with h' | h'
      · exact ⟨0, by norm_num, by rw [cos_val_0]; linarith⟩
      · exact ⟨4, by norm_num, by rw [cos_val_4]; linarith⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · rw [cos_val_0]; exact eigen_two
    · rw [cos_val_1]; exact eigen_sqrt_two
    · rw [cos_val_2]; exact eigen_zero
    · rw [cos_val_3]; exact eigen_neg_sqrt_two
    · rw [cos_val_4]; exact eigen_neg_two
    · rw [cos_val_5]; exact eigen_neg_sqrt_two
    · rw [cos_val_6]; exact eigen_zero
    · rw [cos_val_7]; exact eigen_sqrt_two

/-! ### The characteristic polynomial, i.e. the eigenvalues with multiplicities

We diagonalise the adjacency matrix over `ℂ` using the discrete Fourier (Vandermonde) matrix
built from a primitive `8`-th root of unity. -/

/-- A primitive eighth root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

lemma om_pow_eight : om ^ 8 = 1 := by
  rw [om, ← Complex.exp_nat_mul,
    show ((8 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 8) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I]
  norm_cast
  simp

lemma om_pow_mod (a b : ℕ) (h : a % 8 = b % 8) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 8]
  conv_rhs => rw [← Nat.div_add_mod b 8]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_eight, one_pow, one_pow, h]

lemma om_prim : IsPrimitiveRoot om 8 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 8 (by norm_num)

/-- `ωᵏ + ω⁻ᵏ = 2 cos (2πk/8)`. -/
lemma om_sum (k : ℕ) : om ^ k + om ^ (7 * k) = ((2 * Real.cos (2 * Real.pi * k / 8) : ℝ) : ℂ) := by
  set x : ℂ := ((2 * Real.pi * k / 8 : ℝ) : ℂ) with hx
  have h1 : om ^ k = Complex.exp (x * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul, hx]
    congr 1
    push_cast; ring
  have hk : om ^ k ≠ 0 := by rw [h1]; exact Complex.exp_ne_zero _
  have h2 : om ^ (7 * k) = Complex.exp (-(x * Complex.I)) := by
    have e1 : om ^ (7 * k) * om ^ k = 1 := by
      rw [← pow_add, show 7 * k + k = 8 * k by ring, pow_mul, om_pow_eight, one_pow]
    have e2 : Complex.exp (-(x * Complex.I)) * om ^ k = 1 := by
      rw [h1, ← Complex.exp_add]; simp
    exact mul_right_cancel₀ hk (e1.trans e2.symm)
  rw [h1, h2, Complex.exp_mul_I, show -(x * Complex.I) = (-x) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, hx]
  push_cast
  ring

/-- The Fourier (Vandermonde) matrix of the eighth roots of unity. -/
noncomputable def Pv : Matrix (Fin 8) (Fin 8) ℂ := Matrix.vandermonde (fun k : Fin 8 => om ^ (k : ℕ))

/-- The diagonal matrix of the numbers `2 cos (2πk/8)`. -/
noncomputable def Dg : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (fun k : Fin 8 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ))

lemma Pv_apply (i k : Fin 8) : Pv i k = om ^ ((i : ℕ) * (k : ℕ)) := by
  rw [Pv, Matrix.vandermonde_apply, pow_mul]

lemma Pv_det_ne_zero : Pv.det ≠ 0 := by
  rw [Pv, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  rw [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  exact absurd (Fin.ext (om_prim.pow_inj j.isLt i.isLt h)) (ne_of_gt hj)

/-- The complex adjacency matrix is conjugated to the diagonal matrix of the numbers
`2 cos (2πk/8)` by the Fourier matrix. -/
lemma adjMatrix_mul_Pv : ((SimpleGraph.cycleGraph 8).adjMatrix ℂ) * Pv = Pv * Dg := by
  ext i k
  have hL : (((SimpleGraph.cycleGraph 8).adjMatrix ℂ) * Pv) i k = Pv (i - 1) k + Pv (i + 1) k := by
    rw [Matrix.mul_apply,
      show (∑ j, ((SimpleGraph.cycleGraph 8).adjMatrix ℂ) i j * Pv j k)
        = (((SimpleGraph.cycleGraph 8).adjMatrix ℂ) *ᵥ (fun j => Pv j k)) i from rfl,
      adj8_mulVec]
  have e1 : om ^ ((i - 1 : Fin 8) * k : ℕ) = om ^ ((i : ℕ) * k + 7 * k) := by
    apply om_pow_mod
    have hv : ((i - 1 : Fin 8) : ℕ) = ((i : ℕ) + 7) % 8 := by rw [Fin.sub_def]; simp [Nat.add_comm]
    rw [hv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show ((i : ℕ) + 7) * (k : ℕ) = (i : ℕ) * (k : ℕ) + 7 * (k : ℕ) from by ring]
  have e2 : om ^ ((i + 1 : Fin 8) * k : ℕ) = om ^ ((i : ℕ) * k + k) := by
    apply om_pow_mod
    have hv : ((i + 1 : Fin 8) : ℕ) = ((i : ℕ) + 1) % 8 := by rw [Fin.add_def]; simp
    rw [hv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show ((i : ℕ) + 1) * (k : ℕ) = (i : ℕ) * (k : ℕ) + (k : ℕ) from by ring]
  rw [hL, Dg, Matrix.mul_diagonal, Pv_apply, Pv_apply, Pv_apply, ← om_sum, e1, e2, pow_add, pow_add]
  ring

open Polynomial in
lemma charpoly_adjMatrix_complex :
    ((SimpleGraph.cycleGraph 8).adjMatrix ℂ).charpoly =
      ∏ k : Fin 8, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ)) := by
  have hunit : IsUnit Pv.det := isUnit_iff_ne_zero.2 Pv_det_ne_zero
  have hconj : (SimpleGraph.cycleGraph 8).adjMatrix ℂ =
      ((Matrix.nonsingInvUnit Pv hunit : (Matrix (Fin 8) (Fin 8) ℂ)ˣ) : Matrix (Fin 8) (Fin 8) ℂ) *
        Dg * ((Matrix.nonsingInvUnit Pv hunit)⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ) := by
    show _ = Pv * Dg * Pv⁻¹
    rw [← adjMatrix_mul_Pv, Matrix.mul_assoc, Matrix.mul_nonsing_inv Pv hunit, Matrix.mul_one]
  rw [hconj, Matrix.charpoly_units_conj, Dg, Matrix.charpoly_diagonal]

lemma C8adj_map_complex :
    C8adj.map (Complex.ofRealHom : ℝ →+* ℂ) = (SimpleGraph.cycleGraph 8).adjMatrix ℂ := by
  ext i j
  simp [C8adj, SimpleGraph.adjMatrix, apply_ite (Complex.ofRealHom : ℝ →+* ℂ)]

open Polynomial in
/-- **The Hückel spectrum of C₈ with multiplicities.**  The characteristic polynomial of the
adjacency matrix of the cycle graph `C₈` is `∏_{k=0}^{7} (X - 2 cos (2πk/8))`; equivalently the
eight eigenvalues, listed with multiplicity, are `2 cos (2πk/8)` for `k = 0, …, 7`. -/
theorem huckel_C8_charpoly :
    C8adj.charpoly = ∏ k : Fin 8, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 8))) := by
  refine Polynomial.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective ?_
  rw [← Matrix.charpoly_map, C8adj_map_complex, charpoly_adjMatrix_complex, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

end Chem

