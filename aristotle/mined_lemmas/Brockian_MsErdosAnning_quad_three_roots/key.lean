import Mathlib

/-!
# The Erdős–Anning theorem

An infinite set of points in the Euclidean plane whose pairwise distances are all integers
must be collinear.

## Proof outline

Assume `S` is infinite with integral pairwise distances and pick `A ≠ B` in `S`.  If some
`C ∈ S` is off the line `AB`, then `A`, `B`, `C` form a non-degenerate triangle.  For every
`P ∈ S` the two differences `dist P A - dist P B` and `dist P A - dist P C` are integers
bounded in absolute value by `dist A B` and `dist A C` respectively, so only finitely many
pairs of values occur (`finite_of_not_collinear`).  The heart of the argument (`key`) shows
that three *distinct* points cannot share the same pair of differences: writing
`⟪P - A, B - A⟫` in terms of the distances (`inner_formula`) shows that all such points lie
on a common line `A + p + x • q` with `x = dist P A`, and `‖p + x • q‖ = x` can hold for at
most two values of `x` unless `p = 0` and `‖q‖ = 1` (`key_p_zero`), in which case `B - A`
and `C - A` are both multiples of `q`, contradicting non-collinearity.  Hence `S` would be
finite, a contradiction.
-/

namespace Brockian.MsErdosAnning

open scoped RealInnerProductSpace

/-! ### Auxiliary algebraic lemmas -/

/-- A real quadratic with three distinct roots is identically zero. -/

lemma key {A B C P Q R : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (e1Q : dist Q A - dist Q B = dist P A - dist P B)
    (e1R : dist R A - dist R B = dist P A - dist P B)
    (e2Q : dist Q A - dist Q C = dist P A - dist P C)
    (e2R : dist R A - dist R C = dist P A - dist P C) : False := by
  obtain ⟨q, hq1, hq2⟩ := exists_inner_eq hABC (dist P A - dist P B) (dist P A - dist P C)
  have hPQ' := same_p hABC hq1 hq2 e1Q e2Q
  have hPR' := same_p hABC hq1 hq2 e1R e2R
  have hPQ_vec : P - Q = (dist P A - dist Q A) • q := by
    have eq1 : P - A - dist P A • q - (Q - A - dist Q A • q) = 0 := by rw [hPQ']; abel
    have eq2 : (P - Q) - (dist P A - dist Q A) • q = 0 := by convert eq1 using 1; module
    exact sub_eq_zero.mp eq2
  have hpq : dist P A ≠ dist Q A := by
    intro h
    simp [h] at hPQ_vec
    exact hPQ (sub_eq_zero.mp hPQ_vec)
  have hqr : dist Q A ≠ dist R A := by
    intro h
    have hQR_vec : Q - R = (dist Q A - dist R A) • q := by
      have eq1 : Q - A - dist Q A • q = R - A - dist R A • q := by rw [hPQ'.symm, hPR']
      have eq2 : Q - A - dist Q A • q - (R - A - dist R A • q) = 0 := by rw [eq1]; abel
      have eq3 : (Q - R) - (dist Q A - dist R A) • q = 0 := by convert eq2 using 1; module
      exact sub_eq_zero.mp eq3
    simp [h] at hQR_vec
    exact hQR (sub_eq_zero.mp hQR_vec)
  have hpr_vec : P - R = (dist P A - dist R A) • q := by
    have eq1 : P - A - dist P A • q - (R - A - dist R A • q) = 0 := by rw [hPR']; abel
    have eq2 : (P - R) - (dist P A - dist R A) • q = 0 := by convert eq1 using 1; module
    exact sub_eq_zero.mp eq2
  have hpr : dist P A ≠ dist R A := by
    intro h
    simp [h] at hpr_vec
    exact hPR (sub_eq_zero.mp hpr_vec)
  have hQR_vec : Q - R = (dist Q A - dist R A) • q := by
    have eq1 : Q - A - dist Q A • q = R - A - dist R A • q := by rw [hPQ'.symm, hPR']
    have eq2 : Q - A - dist Q A • q - (R - A - dist R A • q) = 0 := by rw [eq1]; abel
    have eq3 : (Q - R) - (dist Q A - dist R A) • q = 0 := by convert eq2 using 1; module
    exact sub_eq_zero.mp eq3
  let c_Q := ⟪Q - A, q⟫
  let s := ‖q‖^2
  have hPQ_sq : dist P A ^ 2 = dist Q A ^ 2 + 2 * (dist P A - dist Q A) * c_Q + (dist P A - dist Q A) ^ 2 * s := by
    have hPQ_eq : P - A = Q - A + (dist P A - dist Q A) • q := by
      have : P - Q = (dist P A - dist Q A) • q := hPQ_vec
      calc P - A = (P - Q) + (Q - A) := by module
        _ = (dist P A - dist Q A) • q + (Q - A) := by rw [this]
        _ = Q - A + (dist P A - dist Q A) • q := by module
    have h1 : dist P A ^ 2 = ‖P - A‖ ^ 2 := by rw [dist_eq_norm]
    have h2 : dist Q A ^ 2 = ‖Q - A‖ ^ 2 := by rw [dist_eq_norm]
    rw [h1, h2, hPQ_eq, norm_add_sq_real, inner_smul_right, norm_smul]
    simp [s]
    rw [mul_pow, sq_abs]
    ring
  have hPR_sq : dist P A ^ 2 = dist R A ^ 2 + 2 * (dist P A - dist R A) * ⟪R - A, q⟫ + (dist P A - dist R A) ^ 2 * s := by
    have hPR_eq : P - A = R - A + (dist P A - dist R A) • q := by
      have : P - R = (dist P A - dist R A) • q := hpr_vec
      calc P - A = (P - R) + (R - A) := by module
        _ = (dist P A - dist R A) • q + (R - A) := by rw [this]
        _ = R - A + (dist P A - dist R A) • q := by module
    have h1 : dist P A ^ 2 = ‖P - A‖ ^ 2 := by rw [dist_eq_norm]
    have h2 : dist R A ^ 2 = ‖R - A‖ ^ 2 := by rw [dist_eq_norm]
    rw [h1, h2, hPR_eq, norm_add_sq_real, inner_smul_right, norm_smul]
    simp [s]
    rw [mul_pow, sq_abs]
    ring
  have hQR_sq : dist Q A ^ 2 = dist R A ^ 2 + 2 * (dist Q A - dist R A) * ⟪R - A, q⟫ + (dist Q A - dist R A) ^ 2 * s := by
    have hQR_eq : Q - A = R - A + (dist Q A - dist R A) • q := by
      have : Q - R = (dist Q A - dist R A) • q := hQR_vec
      calc Q - A = (Q - R) + (R - A) := by module
        _ = (dist Q A - dist R A) • q + (R - A) := by rw [this]
        _ = R - A + (dist Q A - dist R A) • q := by module
    have h1 : dist Q A ^ 2 = ‖Q - A‖ ^ 2 := by rw [dist_eq_norm]
    have h2 : dist R A ^ 2 = ‖R - A‖ ^ 2 := by rw [dist_eq_norm]
    rw [h1, h2, hQR_eq, norm_add_sq_real, inner_smul_right, norm_smul]
    simp [s]
    rw [mul_pow, sq_abs]
    ring
  let a := dist P A
  let b := dist Q A
  let c := dist R A
  let cQ := ⟪Q - A, q⟫
  let cR := ⟪R - A, q⟫
  have hPQcQ : a ^ 2 = b ^ 2 + 2 * (a - b) * cQ + (a - b) ^ 2 * s := hPQ_sq
  have hQRcR : b ^ 2 = c ^ 2 + 2 * (b - c) * cR + (b - c) ^ 2 * s := hQR_sq
  have hPRcR : a ^ 2 = c ^ 2 + 2 * (a - c) * cR + (a - c) ^ 2 * s := hPR_sq
  have hPQcR : a ^ 2 = c ^ 2 + 2 * (a - b) * cQ + 2 * (b - c) * cR + (a - b) ^ 2 * s + (b - c) ^ 2 * s := by
    linarith
  have eq2 : b + c = 2 * cR + (b - c) * s := by
    have factored : b ^ 2 - c ^ 2 = (b - c) * (2 * cR + (b - c) * s) := by ring_nf; linarith
    have key : (b - c) * (b + c) = (b - c) * (2 * cR + (b - c) * s) := by ring_nf; linarith
    exact mul_left_cancel₀ (sub_ne_zero.mpr hqr) key
  have eq3 : a + c = 2 * cR + (a - c) * s := by
    have factored : a ^ 2 - c ^ 2 = (a - c) * (2 * cR + (a - c) * s) := by ring_nf; linarith
    have key : (a - c) * (a + c) = (a - c) * (2 * cR + (a - c) * s) := by ring_nf; linarith
    exact mul_left_cancel₀ (sub_ne_zero.mpr hpr) key
  have hProd1 : (a - b) * (1 - s) = 0 := by
    have sub_eq : a - b = (a - b) * s := by linarith
    linear_combination sub_eq
  have hs_eq : s = 1 := by
    have := mul_eq_zero.mp hProd1
    cases this with
    | inl h => exact absurd h (sub_ne_zero.mpr hpq)
    | inr h => linarith
  have hq_norm : ‖q‖ = 1 := by
    have hs_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
    simp [s] at hs_eq
    cases hs_eq with
    | inl h => exact h
    | inr h => linarith
  have hcQ : c_Q = b := by
    have h := hPQcQ
    simp [s, hs_eq] at h
    have factored : (a - b) * (c_Q - b) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp factored).resolve_left (sub_ne_zero.mpr hpq))
  have hcR : cR = c := by
    simp [s, hs_eq] at eq2
    linarith
  have hQA_vec : Q - A = b • q := by
    apply eq_smul_of_norm_one hq_norm
    · rw [real_inner_comm]; exact hcQ
    · simp [dist_eq_norm, b]
  have hRA_vec : R - A = c • q := by
    apply eq_smul_of_norm_one hq_norm
    · rw [real_inner_comm]; exact hcR
    · simp [dist_eq_norm, c]
  have hPA_vec : P - A = a • q := by
    calc P - A = (P - Q) + (Q - A) := by module
      _ = (a - b) • q + b • q := by rw [hPQ_vec, hQA_vec]
      _ = a • q := by rw [sub_smul]; simp
  have hd_sq : (⟪q, B - A⟫) ^ 2 = dist A B ^ 2 := by
    have hPB_eq : P - B = (A - B) + a • q := by
      have : P - B = (P - A) + (A - B) := by module
      rw [this, hPA_vec]
      abel
    have hPB_sq : dist P B ^ 2 = dist A B ^ 2 - 2 * ⟪q, B - A⟫ * a + a ^ 2 := by
      have h1 : dist P B ^ 2 = ‖P - B‖ ^ 2 := by rw [dist_eq_norm]
      rw [h1, hPB_eq, norm_add_sq_real, inner_smul_right, norm_smul]
      simp [hq_norm]
      rw [dist_eq_norm]
      have hBAsub : ⟪q, B - A⟫ = -⟪q, A - B⟫ := by
        have : B - A = -(A - B) := by abel
        rw [this, inner_neg_right]
      rw [hBAsub, real_inner_comm q (A - B)]
      ring
    have hd : ⟪q, B - A⟫ = a - dist P B := hq1
    have hd2 : dist P B ^ 2 = dist A B ^ 2 - 2 * a * (a - dist P B) + a ^ 2 := by
      rw [hd] at hPB_sq
      linear_combination hPB_sq
    calc (⟪q, B - A⟫) ^ 2 = (a - dist P B) ^ 2 := by rw [hd]
      _ = a ^ 2 - 2 * a * dist P B + dist P B ^ 2 := by ring
      _ = dist A B ^ 2 := by linarith [hd2]
  have he_sq : (⟪q, C - A⟫) ^ 2 = dist A C ^ 2 := by
    have hPC_eq : P - C = (A - C) + a • q := by
      have : P - C = (P - A) + (A - C) := by module
      rw [this, hPA_vec]
      abel
    have hPC_sq : dist P C ^ 2 = dist A C ^ 2 - 2 * ⟪q, C - A⟫ * a + a ^ 2 := by
      have h1 : dist P C ^ 2 = ‖P - C‖ ^ 2 := by rw [dist_eq_norm]
      rw [h1, hPC_eq, norm_add_sq_real, inner_smul_right, norm_smul]
      simp [hq_norm]
      rw [dist_eq_norm]
      have hCAsub : ⟪q, C - A⟫ = -⟪q, A - C⟫ := by
        have : C - A = -(A - C) := by abel
        rw [this, inner_neg_right]
      rw [hCAsub, real_inner_comm q (A - C)]
      ring
    have he : ⟪q, C - A⟫ = a - dist P C := hq2
    have he2 : dist P C ^ 2 = dist A C ^ 2 - 2 * a * (a - dist P C) + a ^ 2 := by
      rw [he] at hPC_sq
      linear_combination hPC_sq
    calc (⟪q, C - A⟫) ^ 2 = (a - dist P C) ^ 2 := by rw [he]
      _ = a ^ 2 - 2 * a * dist P C + dist P C ^ 2 := by ring
      _ = dist A C ^ 2 := by linarith [he2]
  have hBA_par : ∃ r : ℝ, B - A = r • q := by
    use ⟪B - A, q⟫
    apply eq_smul_of_norm_one hq_norm (real_inner_comm _ _)
    rw [dist_eq_norm] at hd_sq
    rw [real_inner_comm] at hd_sq
    rw [norm_sub_rev] at hd_sq
    exact hd_sq.symm
  have hCA_par : ∃ t : ℝ, C - A = t • q := by
    use ⟪C - A, q⟫
    apply eq_smul_of_norm_one hq_norm (real_inner_comm _ _)
    rw [dist_eq_norm] at he_sq
    rw [real_inner_comm] at he_sq
    rw [norm_sub_rev] at he_sq
    exact he_sq.symm
  obtain ⟨r, hr⟩ := hBA_par
  obtain ⟨t, ht⟩ := hCA_par
  by_cases ht0 : t = 0
  · simp [ht0] at ht
    have hCA : C = A := sub_eq_zero.mp ht
    simp [hCA] at hABC
    exact hABC (collinear_pair ℝ B A)
  · have hBA_par_C : B - A = (r / t) • (C - A) := by
      rw [hr, ht]
      rw [smul_smul]
      congr 1
      field_simp
    have hcoll : Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      use A, C - A
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨r / t, by rw [← hBA_par_C]; simp⟩
      · exact ⟨1, by simp⟩
    exact hABC hcoll
/-- Any distance difference within `S` is an integer. -/
