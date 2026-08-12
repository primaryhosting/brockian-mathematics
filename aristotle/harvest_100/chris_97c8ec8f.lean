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

namespace Brockian

/-! # The `CosTraceNorm` family

For an angle `t` and `n : ℕ` we study the truncated cosine trace
`cosTrace n t = ∑_{k < n} cos (k t)`, which is (half) the trace of the geometric sum
`∑_{k < n} R(t)^k` of powers of the planar rotation matrix `R(t)`.

The corresponding "trace norm" is the Schatten-1 norm of that operator, which for
these normal `2 × 2` matrices equals `2 * ‖∑_{k<n} e^{ikt}‖`, i.e. twice the
Dirichlet quotient `|sin (n t / 2)| / |sin (t / 2)|`.

The main result `Brockian.CosTraceNorm1597` bounds `|cosTrace n t|` by the minimum of
the trivial bound `n` and the Dirichlet trace norm.
-/

/-- The truncated cosine trace `∑_{k<n} cos (k t)`. -/
noncomputable def cosTrace (n : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range n, Real.cos (k * t)

/-- The truncated sine trace `∑_{k<n} sin (k t)`. -/
noncomputable def sinTrace (n : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range n, Real.sin (k * t)

/-- The Dirichlet trace norm `|sin (n t / 2)| / |sin (t / 2)|`. -/
noncomputable def dirichletTraceNorm (n : ℕ) (t : ℝ) : ℝ :=
  |Real.sin (n * t / 2)| / |Real.sin (t / 2)|

/-- The planar rotation matrix by the angle `t`. -/
noncomputable def rot (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

/-- The complex exponential sum `∑_{k<n} e^{i k t}`. -/
noncomputable def expSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, Complex.exp ((k * t : ℝ) * Complex.I)

/-! ## Basic identities -/

theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul' (θ / 2)
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    have e : (2 : ℝ) * (θ / 2) = θ := by ring
    rw [e] at h; nlinarith
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    have e : (2 : ℝ) * (θ / 2) = θ := by ring
    rw [e] at h; linarith
  have hrhs : 2 * |Real.sin (θ / 2)| = Real.sqrt (4 * Real.sin (θ / 2) ^ 2) := by
    rw [show (4 : ℝ) * Real.sin (θ / 2) ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 from by
      rw [mul_pow, sq_abs]; ring]
    exact (Real.sqrt_sq (by positivity)).symm
  rw [Complex.exp_mul_I, Complex.norm_def, Complex.normSq_apply, hrhs]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    hc, hs]
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

theorem rot_mul_rot (s t : ℝ) : rot s * rot t = rot (s + t) := by
  simp only [rot, Real.cos_add, Real.sin_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rot_pow (k : ℕ) (t : ℝ) : rot t ^ k = rot (k * t) := by
  induction k with
  | zero => simp [rot, Matrix.one_fin_two]
  | succ m ih =>
      rw [pow_succ, ih, rot_mul_rot]
      congr 1
      push_cast
      ring

/-- The cosine trace really is a trace: it is half the trace of the geometric sum of
rotation matrices. -/
theorem cosTrace_eq_half_trace_rot (n : ℕ) (t : ℝ) :
    cosTrace n t = (∑ k ∈ Finset.range n, rot t ^ k).trace / 2 := by
  rw [Matrix.trace_sum, Finset.sum_div, cosTrace]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [rot_pow]
  simp [rot, Matrix.trace_fin_two]

theorem expSum_re (n : ℕ) (t : ℝ) : (expSum n t).re = cosTrace n t := by
  rw [expSum, Complex.re_sum, cosTrace]
  exact Finset.sum_congr rfl (fun k _ => Complex.exp_ofReal_mul_I_re _)

theorem expSum_im (n : ℕ) (t : ℝ) : (expSum n t).im = sinTrace n t := by
  rw [expSum, Complex.im_sum, sinTrace]
  exact Finset.sum_congr rfl (fun k _ => Complex.exp_ofReal_mul_I_im _)

/-! ## The trace norm -/

/-- The modulus of the exponential sum is the Dirichlet trace norm. -/
theorem norm_expSum (n : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    ‖expSum n t‖ = dirichletTraceNorm n t := by
  set z : ℂ := Complex.exp ((t : ℂ) * Complex.I) with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    have := norm_exp_mul_I_sub_one t
    rw [← hzdef, h] at this
    simp at this
    exact ht (by simpa using this)
  have hgeom : expSum n t = ∑ k ∈ Finset.range n, z ^ k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzn : z ^ n = Complex.exp (((n * t : ℝ) : ℂ) * Complex.I) := by
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hgeom, geom_sum_eq hz1, norm_div, hzn, norm_exp_mul_I_sub_one, norm_exp_mul_I_sub_one,
    dirichletTraceNorm]
  rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- Pythagoras for the cosine and sine traces. -/
theorem cosTrace_sq_add_sinTrace_sq (n : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    cosTrace n t ^ 2 + sinTrace n t ^ 2 = dirichletTraceNorm n t ^ 2 := by
  rw [← norm_expSum n t ht, ← expSum_re, ← expSum_im, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

/-! ## Bounds -/

theorem abs_cosTrace_le_card (n : ℕ) (t : ℝ) : |cosTrace n t| ≤ n := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.range n, |Real.cos (k * t)|
      ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => Real.abs_cos_le_one _)
    _ = n := by simp

theorem abs_cosTrace_le_dirichletTraceNorm (n : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    |cosTrace n t| ≤ dirichletTraceNorm n t := by
  rw [← norm_expSum n t ht, ← expSum_re]
  exact Complex.abs_re_le_norm _

/-- **Main theorem.** The truncated cosine trace is bounded by the minimum of the trivial
bound `n` and the Dirichlet trace norm `|sin (n t / 2)| / |sin (t / 2)|`. -/
theorem CosTraceNorm1597 (n : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    |cosTrace n t| ≤ min (n : ℝ) (dirichletTraceNorm n t) :=
  le_min (abs_cosTrace_le_card n t) (abs_cosTrace_le_dirichletTraceNorm n t ht)

/-- Uniform-in-`n` corollary: the cosine traces are bounded by `1 / |sin (t/2)|`. -/
theorem abs_cosTrace_le_inv_abs_sin (n : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    |cosTrace n t| ≤ 1 / |Real.sin (t / 2)| := by
  refine (abs_cosTrace_le_dirichletTraceNorm n t ht).trans ?_
  have hpos : 0 < |Real.sin (t / 2)| := abs_pos.mpr ht
  rw [dirichletTraceNorm]
  gcongr
  exact Real.abs_sin_le_one _

/-- Jordan's inequality in the form needed for the half-angle: for `|t| ≤ π`,
`|t| / π ≤ |sin (t / 2)|`. -/
theorem abs_div_pi_le_abs_sin_half {t : ℝ} (ht : |t| ≤ Real.pi) :
    |t| / Real.pi ≤ |Real.sin (t / 2)| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨hl, hr⟩ := abs_le.mp ht
  have habs : |Real.sin (t / 2)| = Real.sin (|t| / 2) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    · have hn : 0 ≤ Real.sin (-(t / 2)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at hn
      rw [abs_of_nonpos (by linarith), abs_of_neg h, show -t / 2 = -(t / 2) by ring, Real.sin_neg]
  rw [habs]
  have h2 : 2 / Real.pi * (|t| / 2) ≤ Real.sin (|t| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  calc |t| / Real.pi = 2 / Real.pi * (|t| / 2) := by field_simp
    _ ≤ Real.sin (|t| / 2) := h2

/-- Jordan-type trace-norm bound: for `0 < |t| ≤ π` the cosine traces are bounded by `π / |t|`,
uniformly in `n`. -/
theorem abs_cosTrace_le_pi_div_abs (n : ℕ) (t : ℝ) (ht0 : t ≠ 0) (ht : |t| ≤ Real.pi) :
    |cosTrace n t| ≤ Real.pi / |t| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlow : |t| / Real.pi ≤ |Real.sin (t / 2)| := abs_div_pi_le_abs_sin_half ht
  have hspos : 0 < |Real.sin (t / 2)| := lt_of_lt_of_le (by positivity) hlow
  have hs : Real.sin (t / 2) ≠ 0 := by
    intro h; rw [h] at hspos; simp at hspos
  refine (abs_cosTrace_le_inv_abs_sin n t hs).trans ?_
  calc 1 / |Real.sin (t / 2)| ≤ 1 / (|t| / Real.pi) :=
        one_div_le_one_div_of_le (by positivity) hlow
    _ = Real.pi / |t| := one_div_div _ _

end Brockian

