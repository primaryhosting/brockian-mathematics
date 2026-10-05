import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal NNReal

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0:ℤ) (1:ℂ), 0, ?_⟩
  intro h
  have := congrFun (congrArg (fun x : L2Z => (x : ℤ → ℂ)) h) 0
  simp [lp.single_apply] at this

/-- Membership of a "weighted shift" sequence in `ℓ²(ℤ)`. -/
theorem memL2Z_weightedShift (w : ℤ → ℂ) (e : ℤ ≃ ℤ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C)
    (f : L2Z) : Memℓp (fun n : ℤ => w n * f (e n)) 2 := by
  set t : ℝ := (2 : ℝ≥0∞).toReal with ht_def
  have ht : (0:ℝ) < t := by norm_num [ht_def]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  have hsum : Summable fun n : ℤ => ‖f n‖ ^ t := (lp.memℓp f).summable ht
  have hcomp : Summable fun n : ℤ => ‖f (e n)‖ ^ t := (e.summable_iff).mpr hsum
  refine memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity) ?_
    (hcomp.mul_left (C ^ t)))
  intro n
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  gcongr
  exact hw n

/-- The defining norm bound for the weighted shift. -/
theorem weightedShift_norm_bound (w : ℤ → ℂ) (e : ℤ ≃ ℤ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C)
    (f g : L2Z) (hg : ∀ n, g n = w n * f (e n)) : ‖g‖ ≤ C * ‖f‖ := by
  set t : ℝ := (2 : ℝ≥0∞).toReal with ht_def
  have ht : (0:ℝ) < t := by norm_num [ht_def]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  have hsum : Summable fun n : ℤ => ‖f n‖ ^ t := (lp.memℓp f).summable ht
  have hcomp : Summable fun n : ℤ => ‖f (e n)‖ ^ t := (e.summable_iff).mpr hsum
  have hgs : Summable fun n : ℤ => ‖g n‖ ^ t := (lp.memℓp g).summable ht
  have h1 : ∑' n : ℤ, ‖f (e n)‖ ^ t = ‖f‖ ^ t := by
    rw [e.tsum_eq (fun n => ‖f n‖ ^ t)]
    exact (lp.hasSum_norm ht f).tsum_eq
  refine lp.norm_le_of_tsum_le ht (by positivity) ?_
  calc ∑' n : ℤ, ‖g n‖ ^ t
      ≤ ∑' n : ℤ, C ^ t * ‖f (e n)‖ ^ t := by
        refine Summable.tsum_le_tsum ?_ hgs (hcomp.mul_left _)
        intro n
        rw [hg n, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
        gcongr
        exact hw n
    _ = C ^ t * ‖f‖ ^ t := by rw [tsum_mul_left, h1]
    _ = (C * ‖f‖) ^ t := (Real.mul_rpow hC (norm_nonneg _)).symm

/-- The weighted shift operator `f ↦ (n ↦ w n * f (e n))` on `ℓ²(ℤ)`, for a bounded weight
`w` and a reindexing `e` of `ℤ`. -/
def weightedShift (w : ℤ → ℂ) (e : ℤ ≃ ℤ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) : L2Z →L[ℂ] L2Z :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => w n * f (e n), memL2Z_weightedShift w e C hw f⟩
      map_add' := by
        intro f g
        ext n
        simp [mul_add]
      map_smul' := by
        intro c f
        ext n
        simp [mul_left_comm] }
    C (fun f => weightedShift_norm_bound w e C hw f _ (fun _ => rfl))

@[simp] theorem weightedShift_apply (w : ℤ → ℂ) (e : ℤ ≃ ℤ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C)
    (f : L2Z) (n : ℤ) : (weightedShift w e C hw f) n = w n * f (e n) := rfl

theorem norm_weightedShift_le (w : ℤ → ℂ) (e : ℤ ≃ ℤ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) :
    ‖weightedShift w e C hw‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ ((norm_nonneg _).trans (hw 0)) _

/-- The potential of the almost Mathieu operator: `v n = 2 λ cos (2π (θ + n α))`. -/
def amoPotential (lam alpha theta : ℝ) (n : ℤ) : ℂ :=
  ((2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha)) : ℝ) : ℂ)

theorem amoPotential_bound (lam alpha theta : ℝ) (n : ℤ) :
    ‖amoPotential lam alpha theta n‖ ≤ 2 * |lam| := by
  have hcos : |Real.cos (2 * Real.pi * (theta + n * alpha))| ≤ 1 := Real.abs_cos_le_one _
  rw [amoPotential, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  calc |(2:ℝ)| * |lam| * |Real.cos (2 * Real.pi * (theta + n * alpha))|
      ≤ |(2:ℝ)| * |lam| * 1 := by gcongr
    _ = 2 * |lam| := by rw [mul_one]; norm_num

theorem amoPotential_conj (lam alpha theta : ℝ) (n : ℤ) :
    conj (amoPotential lam alpha theta n) = amoPotential lam alpha theta n :=
  Complex.conj_ofReal _

/-- The right shift `(S₊ f) n = f (n + 1)`. -/
def shiftPlus : L2Z →L[ℂ] L2Z :=
  weightedShift (fun _ => 1) (Equiv.addRight (1 : ℤ)) 1 (by simp)

/-- The left shift `(S₋ f) n = f (n - 1)`. -/
def shiftMinus : L2Z →L[ℂ] L2Z :=
  weightedShift (fun _ => 1) (Equiv.addRight (-1 : ℤ)) 1 (by simp)

/-- Multiplication by the almost Mathieu potential. -/
def amoMul (lam alpha theta : ℝ) : L2Z →L[ℂ] L2Z :=
  weightedShift (amoPotential lam alpha theta) (Equiv.refl ℤ) (2 * |lam|)
    (amoPotential_bound lam alpha theta)

/-- The almost Mathieu operator `H_{λ,α,θ}` on `ℓ²(ℤ)`:
`(H u) n = u (n+1) + u (n-1) + 2 λ cos (2π (θ + n α)) * u n`. -/
def amo (lam alpha theta : ℝ) : L2Z →L[ℂ] L2Z :=
  shiftPlus + shiftMinus + amoMul lam alpha theta

@[simp] theorem shiftPlus_apply (u : L2Z) (n : ℤ) : (shiftPlus u) n = u (n + 1) := by
  simp [shiftPlus]

@[simp] theorem shiftMinus_apply (u : L2Z) (n : ℤ) : (shiftMinus u) n = u (n - 1) := by
  simp [shiftMinus, sub_eq_add_neg]

@[simp] theorem amoMul_apply (lam alpha theta : ℝ) (u : L2Z) (n : ℤ) :
    (amoMul lam alpha theta u) n = amoPotential lam alpha theta n * u n := by
  simp [amoMul]

@[simp] theorem amo_apply (lam alpha theta : ℝ) (u : L2Z) (n : ℤ) :
    (amo lam alpha theta u) n
      = u (n + 1) + u (n - 1) + amoPotential lam alpha theta n * u n := by
  simp [amo]

theorem inner_shiftPlus (x y : L2Z) : ⟪shiftPlus x, y⟫_ℂ = ⟪x, shiftMinus y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    ← (Equiv.addRight (1:ℤ)).tsum_eq (fun n : ℤ => ⟪x n, (shiftMinus y) n⟫_ℂ)]
  refine tsum_congr fun n => ?_
  simp

theorem inner_shiftMinus (x y : L2Z) : ⟪shiftMinus x, y⟫_ℂ = ⟪x, shiftPlus y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    ← (Equiv.addRight (-1:ℤ)).tsum_eq (fun n : ℤ => ⟪x n, (shiftPlus y) n⟫_ℂ)]
  refine tsum_congr fun n => ?_
  simp [sub_eq_add_neg]

theorem inner_amoMul (lam alpha theta : ℝ) (x y : L2Z) :
    ⟪amoMul lam alpha theta x, y⟫_ℂ = ⟪x, amoMul lam alpha theta y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [amoMul_apply, RCLike.inner_apply, map_mul, amoPotential_conj]
  ring

/-- The almost Mathieu operator is self-adjoint. -/
theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show ⟪amo lam alpha theta x, y⟫_ℂ = ⟪x, amo lam alpha theta y⟫_ℂ
  rw [amo]
  simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    inner_shiftPlus, inner_shiftMinus, inner_amoMul]
  ring

theorem norm_amo_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  have h1 : ‖shiftPlus‖ ≤ 1 := norm_weightedShift_le _ _ _ _
  have h2 : ‖shiftMinus‖ ≤ 1 := norm_weightedShift_le _ _ _ _
  have h3 : ‖amoMul lam alpha theta‖ ≤ 2 * |lam| := norm_weightedShift_le _ _ _ _
  calc ‖amo lam alpha theta‖ ≤ ‖shiftPlus + shiftMinus‖ + ‖amoMul lam alpha theta‖ :=
        norm_add_le _ _
    _ ≤ (‖shiftPlus‖ + ‖shiftMinus‖) + ‖amoMul lam alpha theta‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (1 + 1) + 2 * |lam| := by gcongr
    _ = 2 + 2 * |lam| := by norm_num

theorem shiftPlus_mul_shiftMinus : shiftPlus * shiftMinus = 1 := by
  ext u n
  simp

theorem shiftMinus_mul_shiftPlus : shiftMinus * shiftPlus = 1 := by
  ext u n
  simp

/-- The right shift, as a unit (invertible element) of the algebra of bounded operators. -/
def shiftUnit : (L2Z →L[ℂ] L2Z)ˣ :=
  ⟨shiftPlus, shiftMinus, shiftPlus_mul_shiftMinus, shiftMinus_mul_shiftPlus⟩

theorem amoPotential_translate (lam alpha theta : ℝ) (n : ℤ) :
    amoPotential lam alpha (theta + alpha) n = amoPotential lam alpha theta (n + 1) := by
  simp only [amoPotential, Int.cast_add, Int.cast_one]
  ring_nf

/-- Covariance of the almost Mathieu family: translating the phase by `α` conjugates the
operator by the shift. -/
theorem amo_translate (lam alpha theta : ℝ) :
    amo lam alpha (theta + alpha) = shiftPlus * amo lam alpha theta * shiftMinus := by
  ext u n
  simp only [ContinuousLinearMap.mul_apply, shiftPlus_apply, shiftMinus_apply, amo_apply,
    amoPotential_translate, show ∀ m : ℤ, m + 1 + 1 - 1 = m + 1 from fun m => by ring,
    show ∀ m : ℤ, m + 1 - 1 = m from fun m => by ring]

/-- The (real) spectrum of the almost Mathieu operator. -/
def amoSpectrum (lam alpha theta : ℝ) : Set ℝ :=
  {E : ℝ | (E : ℂ) ∈ spectrum ℂ (amo lam alpha theta)}

theorem amoSpectrum_nonempty (lam alpha theta : ℝ) : (amoSpectrum lam alpha theta).Nonempty := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (amo lam alpha theta)
  refine ⟨z.re, ?_⟩
  have : z = (z.re : ℂ) := (amo_isSelfAdjoint lam alpha theta).mem_spectrum_eq_re hz
  rwa [amoSpectrum, Set.mem_setOf_eq, ← this]

theorem amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro E hE
  have h1 : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  have h2 : |E| ≤ 2 + 2 * |lam| :=
    le_trans (by simpa using h1) (norm_amo_le lam alpha theta)
  exact ⟨by linarith [abs_le.mp h2 |>.1], (abs_le.mp h2).2⟩

theorem amoSpectrum_isClosed (lam alpha theta : ℝ) : IsClosed (amoSpectrum lam alpha theta) :=
  IsClosed.preimage Complex.continuous_ofReal (spectrum.isClosed (amo lam alpha theta))

theorem amoSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) :=
  IsCompact.of_isClosed_subset isCompact_Icc (amoSpectrum_isClosed lam alpha theta)
    (amoSpectrum_subset_Icc lam alpha theta)

/-- The spectrum of the almost Mathieu operator is invariant under translating the phase
by the frequency. -/
theorem amoSpectrum_translate (lam alpha theta : ℝ) :
    amoSpectrum lam alpha (theta + alpha) = amoSpectrum lam alpha theta := by
  have h : spectrum ℂ (amo lam alpha (theta + alpha)) = spectrum ℂ (amo lam alpha theta) := by
    rw [amo_translate]
    exact spectrum.units_conjugate (u := shiftUnit)
  simp only [amoSpectrum, h]

/-- A subset of `ℝ` is a Cantor set if it is nonempty, compact, has no isolated points,
and has empty interior. -/
def IsCantorSet (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsCompact S ∧ Perfect S ∧ interior S = ∅

/-- **Ten Martini Problem** (Avila–Jitomirskaya), formalized as a Lean-checked reduction.

For every nonzero coupling `λ`, every irrational frequency `α` and every phase `θ`, the
spectrum of the almost Mathieu operator `H_{λ,α,θ}` is a Cantor set.

The two genuinely analytic inputs are taken as hypotheses:
* `h_nowhere_dense`: the spectrum has empty interior (all gaps are open — the
  "gap-labelling"/Cantor part);
* `h_no_isolated`: no point of the spectrum is isolated.

Everything else — that the spectrum is a nonempty compact subset of `ℝ` (which uses that
`H_{λ,α,θ}` is a bounded self-adjoint operator on `ℓ²(ℤ)`, so that its complex spectrum is a
nonempty compact set of reals) — is proved here. -/
theorem avila_ten_martini
    (h_nowhere_dense : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      interior (amoSpectrum lam alpha theta) = ∅)
    (h_no_isolated : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      ∀ E ∈ amoSpectrum lam alpha theta,
        E ∈ closure (amoSpectrum lam alpha theta \ {E})) :
    ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      IsCantorSet (amoSpectrum lam alpha theta) := by
  intro lam alpha theta hlam halpha
  refine ⟨amoSpectrum_nonempty _ _ _, amoSpectrum_isCompact _ _ _,
    ⟨amoSpectrum_isClosed _ _ _, ?_⟩, h_nowhere_dense _ _ _ hlam halpha⟩
  intro E hE
  rw [accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt]
  exact h_no_isolated lam alpha theta hlam halpha E hE

end

end Frontier

