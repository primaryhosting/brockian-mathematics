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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology Submodule Set
open AddCircle (haarAddCircle)

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th Weyl average of `f` along the sequence `x`, i.e.
`(1/N) * ∑_{n < N} f (x n)` (equal to `0` when `N = 0`). -/
noncomputable def weylAvg (x : ℕ → AddCircle T) (f : AddCircle T → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)

/-- A sequence `x` in the circle `ℝ / T ℤ` is *equidistributed* if the Weyl averages of every
continuous function converge to its integral against the normalised Haar (probability) measure. -/
def Equidistributed (x : ℕ → AddCircle T) : Prop :=
  ∀ f : C(AddCircle T, ℂ),
    Tendsto (weylAvg x f) atTop (𝓝 (∫ t : AddCircle T, f t ∂haarAddCircle))

section Basic

/-- Continuous functions on the circle are integrable for the Haar probability measure. -/
lemma integrable_contMap (f : C(AddCircle T, ℂ)) : Integrable f (haarAddCircle (T := T)) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit hT in
lemma weylAvg_sub (x : ℕ → AddCircle T) (f g : AddCircle T → ℂ) (N : ℕ) :
    weylAvg x (f - g) N = weylAvg x f N - weylAvg x g N := by
  simp [weylAvg, Finset.sum_sub_distrib, mul_sub]

omit hT in
lemma weylAvg_add (x : ℕ → AddCircle T) (f g : AddCircle T → ℂ) (N : ℕ) :
    weylAvg x (f + g) N = weylAvg x f N + weylAvg x g N := by
  simp [weylAvg, Finset.sum_add_distrib, mul_add]

omit hT in
lemma weylAvg_smul (x : ℕ → AddCircle T) (c : ℂ) (f : AddCircle T → ℂ) (N : ℕ) :
    weylAvg x (c • f) N = c * weylAvg x f N := by
  simp only [weylAvg, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_assoc, mul_comm ((N : ℂ)⁻¹) c]

/-- The Weyl averages are bounded by the sup norm. -/
lemma norm_weylAvg_le (x : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) (N : ℕ) :
    ‖weylAvg x (⇑f) N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [weylAvg]
  · have h1 : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ (N : ℝ) * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ :=
            Finset.sum_le_sum fun n _ => f.norm_coe_le_norm (x n)
        _ = (N : ℝ) * ‖f‖ := by simp
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [weylAvg, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hNpos]
    exact h1.trans_eq (by ring)

/-- The integral against the Haar probability measure is bounded by the sup norm. -/
lemma norm_integral_le_norm (f : C(AddCircle T, ℂ)) :
    ‖∫ t : AddCircle T, f t ∂haarAddCircle‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (C := ‖f‖) (μ := haarAddCircle (T := T))
    (Eventually.of_forall fun t => f.norm_coe_le_norm t)
  simpa using h

end Basic

/-- The set of continuous functions whose Weyl averages along `x` converge to the integral;
this is a linear subspace of `C(AddCircle T, ℂ)`. -/
noncomputable def equiSubmodule (x : ℕ → AddCircle T) : Submodule ℂ C(AddCircle T, ℂ) where
  carrier := {f : C(AddCircle T, ℂ) |
    Tendsto (weylAvg x (⇑f)) atTop (𝓝 (∫ t : AddCircle T, f t ∂haarAddCircle))}
  zero_mem' := by
    have h0 : weylAvg x (⇑(0 : C(AddCircle T, ℂ))) = fun _ => (0 : ℂ) := by
      funext N; simp [weylAvg]
    have hz : (∫ t : AddCircle T, (0 : C(AddCircle T, ℂ)) t ∂haarAddCircle) = 0 := by simp
    show Tendsto (weylAvg x ⇑(0 : C(AddCircle T, ℂ))) atTop (𝓝 _)
    rw [h0, hz]
    exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    have hint : ∫ t : AddCircle T, (f + g) t ∂haarAddCircle
        = (∫ t : AddCircle T, f t ∂haarAddCircle) + ∫ t : AddCircle T, g t ∂haarAddCircle := by
      simpa using integral_add (integrable_contMap f) (integrable_contMap g)
    rw [hint]
    have hfun : weylAvg x (⇑(f + g)) = fun N => weylAvg x (⇑f) N + weylAvg x (⇑g) N := by
      funext N; simpa using weylAvg_add x (⇑f) (⇑g) N
    rw [hfun]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    have hint : ∫ t : AddCircle T, (c • f) t ∂haarAddCircle
        = c * ∫ t : AddCircle T, f t ∂haarAddCircle := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      simpa using integral_smul c (fun t : AddCircle T => f t) (μ := haarAddCircle)
    rw [hint]
    have hfun : weylAvg x (⇑(c • f)) = fun N => c * weylAvg x (⇑f) N := by
      funext N; simpa using weylAvg_smul x c (⇑f) N
    rw [hfun]
    exact hf.const_mul c

lemma mem_equiSubmodule_iff {x : ℕ → AddCircle T} {f : C(AddCircle T, ℂ)} :
    f ∈ equiSubmodule x ↔
      Tendsto (weylAvg x (⇑f)) atTop (𝓝 (∫ t : AddCircle T, f t ∂haarAddCircle)) :=
  Iff.rfl

/-- Uniform limits preserve the equidistribution property: the subspace is closed. -/
lemma isClosed_equiSubmodule (x : ℕ → AddCircle T) :
    IsClosed ((equiSubmodule x : Submodule ℂ C(AddCircle T, ℂ)) : Set C(AddCircle T, ℂ)) := by
  apply isClosed_of_closure_subset
  intro f hf
  rw [SetLike.mem_coe, mem_equiSubmodule_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgS, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 3) (by linarith)
  rw [SetLike.mem_coe, mem_equiSubmodule_iff, Metric.tendsto_atTop] at hgS
  obtain ⟨N₀, hN₀⟩ := hgS (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖weylAvg x (⇑f) N - weylAvg x (⇑g) N‖ ≤ ‖f - g‖ := by
    have he : weylAvg x (⇑f) N - weylAvg x (⇑g) N = weylAvg x (⇑(f - g)) N := by
      simpa using (weylAvg_sub x (⇑f) (⇑g) N).symm
    rw [he]
    exact norm_weylAvg_le x (f - g) N
  have h3 : ‖(∫ t : AddCircle T, g t ∂haarAddCircle) - ∫ t : AddCircle T, f t ∂haarAddCircle‖
      ≤ ‖g - f‖ := by
    have hint : (∫ t : AddCircle T, g t ∂haarAddCircle)
        - (∫ t : AddCircle T, f t ∂haarAddCircle)
        = ∫ t : AddCircle T, (g - f) t ∂haarAddCircle := by
      simpa using (integral_sub (integrable_contMap g) (integrable_contMap f)).symm
    rw [hint]
    exact norm_integral_le_norm (g - f)
  have hnfg : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  have hngf : ‖g - f‖ < ε / 3 := by
    rw [← dist_eq_norm, dist_comm]; exact hfg
  have h2 : dist (weylAvg x (⇑g) N) (∫ t : AddCircle T, g t ∂haarAddCircle) < ε / 3 := hN₀ N hN
  rw [dist_eq_norm] at h2 ⊢
  calc ‖weylAvg x (⇑f) N - ∫ t : AddCircle T, f t ∂haarAddCircle‖
      = ‖(weylAvg x (⇑f) N - weylAvg x (⇑g) N)
          + (weylAvg x (⇑g) N - ∫ t : AddCircle T, g t ∂haarAddCircle)
          + ((∫ t : AddCircle T, g t ∂haarAddCircle)
              - ∫ t : AddCircle T, f t ∂haarAddCircle)‖ := by ring_nf
    _ ≤ ‖(weylAvg x (⇑f) N - weylAvg x (⇑g) N)
          + (weylAvg x (⇑g) N - ∫ t : AddCircle T, g t ∂haarAddCircle)‖
          + ‖(∫ t : AddCircle T, g t ∂haarAddCircle)
              - ∫ t : AddCircle T, f t ∂haarAddCircle‖ := norm_add_le _ _
    _ ≤ ‖weylAvg x (⇑f) N - weylAvg x (⇑g) N‖
          + ‖weylAvg x (⇑g) N - ∫ t : AddCircle T, g t ∂haarAddCircle‖
          + ‖(∫ t : AddCircle T, g t ∂haarAddCircle)
              - ∫ t : AddCircle T, f t ∂haarAddCircle‖ := by
          gcongr
          exact norm_add_le _ _
    _ < ε := by
          have hA := h1.trans_lt hnfg
          have hB := h3.trans_lt hngf
          linarith

/-- The mean value of a nonzero Fourier character vanishes. -/
lemma integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ t : AddCircle T, fourier k t ∂haarAddCircle = 0 :=
  integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hk hT.out)

/-- The mean value of the trivial character is `1`. -/
lemma integral_fourier_zero :
    ∫ t : AddCircle T, fourier (0 : ℤ) t ∂haarAddCircle = 1 := by
  have h : (fun t : AddCircle T => fourier (0 : ℤ) t) = fun _ => (1 : ℂ) := by
    funext t; exact fourier_zero
  rw [h]
  simp

/-- The trivial character always satisfies the equidistribution conclusion. -/
lemma fourier_zero_mem_equiSubmodule (x : ℕ → AddCircle T) :
    (fourier (0 : ℤ) : C(AddCircle T, ℂ)) ∈ equiSubmodule x := by
  rw [mem_equiSubmodule_iff, integral_fourier_zero]
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)) (f := (atTop : Filter ℕ)))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have hsum : ∑ _n ∈ Finset.range N, (fourier (0 : ℤ) : C(AddCircle T, ℂ)) (x _n) = (N : ℂ) := by
    simp
  rw [weylAvg, hsum, inv_mul_cancel₀ hN0]

/-!
### Main theorem

Weyl's criterion.  The hypothesis of the conditional version — that the linear span of the
characters is dense in `C(AddCircle T, ℂ)` — is discharged unconditionally using Mathlib's
`span_fourier_closure_eq_top` (a consequence of the Stone–Weierstrass theorem), so the statement
below carries no auxiliary assumption beyond the vanishing of the Weyl sums.
-/

/-- **Weyl's equidistribution criterion.**  If for every nonzero integer `k` the Weyl sums
`(1/N) ∑_{n < N} e(k xₙ)` tend to `0`, then the sequence `x` is equidistributed in the circle
`ℝ / T ℤ`: the averages of every continuous function converge to its mean value.

This is unconditional: the density input is supplied by `span_fourier_closure_eq_top`. -/
theorem equidistribution_of_asymptotic {x : ℕ → AddCircle T}
    (h : ∀ k : ℤ, k ≠ 0 → Tendsto (weylAvg x (fourier k)) atTop (𝓝 0)) :
    Equidistributed x := by
  have hspan : span ℂ (Set.range (@fourier T)) ≤ equiSubmodule x := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases eq_or_ne k 0 with rfl | hk
    · exact fourier_zero_mem_equiSubmodule x
    · rw [SetLike.mem_coe, mem_equiSubmodule_iff, integral_fourier_eq_zero hk]
      exact h k hk
  have hle : (span ℂ (Set.range (@fourier T))).topologicalClosure ≤ equiSubmodule x :=
    Submodule.topologicalClosure_minimal _ hspan (isClosed_equiSubmodule x)
  rw [span_fourier_closure_eq_top] at hle
  intro f
  exact hle Submodule.mem_top

/-!
### A non-vacuous instance: irrational rotations

To show that the criterion above is not vacuous we apply it to the classical example of an
irrational rotation.
-/

omit hT in
/-- `fourier k` is a character of the circle. -/
lemma fourier_add_point {k : ℤ} (a b : AddCircle T) :
    fourier k (a + b) = fourier k a * fourier k b := by
  simp [fourier_apply, smul_add, AddCircle.toCircle_add]

omit hT in
lemma fourier_nsmul {k : ℤ} (a : AddCircle T) (n : ℕ) :
    fourier k (n • a) = (fourier k a) ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [succ_nsmul, pow_succ, ← ih, fourier_add_point]

omit hT in
lemma norm_fourier_eq_one {k : ℤ} (a : AddCircle T) : ‖fourier k a‖ = 1 := by
  rw [fourier_apply]; simp

/-- If `α / T` is irrational then no nonzero character is trivial at `α`. -/
lemma fourier_coe_ne_one {a : ℝ} (ha : Irrational (a / T)) {k : ℤ} (hk : k ≠ 0) :
    fourier k ((a : ℝ) : AddCircle T) ≠ 1 := by
  rw [fourier_coe_apply]
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨m, hm⟩ := hcon
  have hTR : (T : ℝ) ≠ 0 := hT.out.ne'
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hTR
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hm
  have keyR : (k : ℝ) * a = T * (m : ℝ) := by exact_mod_cast hm
  refine ha ⟨(m : ℚ) / (k : ℚ), ?_⟩
  push_cast
  field_simp
  linarith [keyR]

/-- **Weyl's equidistribution theorem for irrational rotations.**  If `α / T` is irrational then
the orbit `n ↦ n α` is equidistributed in `ℝ / T ℤ`.  In particular the hypothesis of
`equidistribution_of_asymptotic` is satisfiable. -/
theorem equidistributed_irrational_rotation {a : ℝ} (ha : Irrational (a / T)) :
    Equidistributed (fun n : ℕ => ((n * a : ℝ) : AddCircle T)) := by
  apply equidistribution_of_asymptotic
  intro k hk
  set z : ℂ := fourier k ((a : ℝ) : AddCircle T) with hzdef
  have hz1 : z ≠ 1 := fourier_coe_ne_one ha hk
  have hznorm : ‖z‖ = 1 := norm_fourier_eq_one _
  have hz10 : ‖z - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz1)
  have hterm : ∀ n : ℕ, fourier k ((n * a : ℝ) : AddCircle T) = z ^ n := by
    intro n
    have hcoe : ((n * a : ℝ) : AddCircle T) = n • ((a : ℝ) : AddCircle T) := by
      rw [← nsmul_eq_mul]
      exact (QuotientAddGroup.mk_nsmul _ _ _).symm
    rw [hcoe, hzdef, fourier_nsmul]
  have hbound : ∀ N : ℕ,
      ‖weylAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle T)) (fourier k) N‖
        ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    intro N
    have hsum : weylAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle T)) (fourier k) N
        = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n := by
      rw [weylAvg]
      exact congrArg _ (Finset.sum_congr rfl fun n _ => hterm n)
    rw [hsum, geom_sum_eq hz1, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    gcongr
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hznorm]; norm_num
  refine squeeze_zero_norm hbound ?_
  simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 / ‖z - 1‖)

end Brockian.Equidistribution

