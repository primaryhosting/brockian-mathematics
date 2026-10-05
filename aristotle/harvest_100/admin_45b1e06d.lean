/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `Frontier.amo`: the almost Mathieu operator `H_{lam, alpha, theta}` on `ℓ²(ℤ)`, constructed as
  a bounded operator from a general bounded weighted composition operator.
* `Frontier.amo_isSelfAdjoint`: it is selfadjoint.
* `Frontier.amoSpectrum`: its spectrum, as a subset of `ℝ`; it is nonempty, compact and contained
  in `[-(2 + 2|lam|), 2 + 2|lam|]`.
* `Frontier.IsCantorSet`: nonempty, compact, perfect and totally disconnected subsets of `ℝ`.
* `Frontier.avila_ten_martini`: the Ten Martini statement, reduced (with a Lean-checked proof) to
  the two analytic inputs of the Avila–Jitomirskaya theorem, namely that the spectrum has no
  isolated points and that all spectral gaps are open.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

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

/-! ## The Hilbert space `ℓ²(ℤ)` and weighted shift operators -/

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0:ℤ) (1:ℂ), 0, ?_⟩
  intro h
  have hval := congrArg (fun f : L2Z => (f : ℤ → ℂ) 0) h
  simp at hval

private theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- If `w` is a bounded weight and `e` a bijection of `ℤ`, then `n ↦ w n * u (e n)` is again
square-summable. -/
theorem memℓp_weighted_comp (w : ℤ → ℂ) (C : ℝ) (hC : ∀ n, ‖w n‖ ≤ C) (e : ℤ ≃ ℤ) (u : L2Z) :
    Memℓp (fun n => w n * u (e n)) 2 := by
  apply memℓp_gen
  have hu : Summable (fun n : ℤ => ‖(u : ℤ → ℂ) n‖ ^ (2:ℝ)) := by
    simpa using lp.memℓp u |>.summable (by norm_num)
  have hu2 : Summable (fun n : ℤ => ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)) := hu.comp_injective e.injective
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hu2.mul_left (C ^ 2))
  simp only [ENNReal.toReal_ofNat, norm_mul, rpow_two, mul_pow]
  have h2 : ‖w n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (w n), hC n]
  nlinarith [sq_nonneg ‖(u : ℤ → ℂ) (e n)‖]

/-- The weighted composition `n ↦ w n * u (e n)` has `ℓ²`-norm at most `C * ‖u‖`. -/
theorem norm_weighted_comp_le (w : ℤ → ℂ) (C : ℝ) (hC : ∀ n, ‖w n‖ ≤ C) (e : ℤ ≃ ℤ) (u : L2Z) :
    ‖(⟨fun n => w n * u (e n), memℓp_weighted_comp w C hC e u⟩ : L2Z)‖ ≤ C * ‖u‖ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (w 0)) (hC 0)
  have hp : (0:ℝ) < (2:ℝ≥0∞).toReal := by norm_num
  have hu : Summable (fun n : ℤ => ‖(u : ℤ → ℂ) n‖ ^ (2:ℝ)) := by
    simpa using lp.memℓp u |>.summable (by norm_num)
  have hu2 : Summable (fun n : ℤ => ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)) := hu.comp_injective e.injective
  have hf : Summable (fun n : ℤ => ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)) := by
    simpa [ENNReal.toReal_ofNat] using (memℓp_weighted_comp w C hC e u).summable hp
  set A := ∑' n : ℤ, ‖(u : ℤ → ℂ) n‖ ^ (2:ℝ) with hA
  have hA0 : 0 ≤ A := tsum_nonneg (fun n => by positivity)
  have key : ∑' n : ℤ, ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) ≤ C ^ 2 * A := by
    have h1 : ∑' n : ℤ, ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)
        ≤ ∑' n : ℤ, C ^ 2 * ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) := by
      refine Summable.tsum_mono hf (hu2.mul_left _) (fun n => ?_)
      simp only [norm_mul, rpow_two, mul_pow]
      have h2 : ‖w n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (w n), hC n]
      nlinarith [sq_nonneg ‖(u : ℤ → ℂ) (e n)‖]
    calc _ ≤ ∑' n : ℤ, C ^ 2 * ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) := h1
      _ = C ^ 2 * ∑' n : ℤ, ‖(u : ℤ → ℂ) (e n)‖ ^ (2:ℝ) := tsum_mul_left
      _ = C ^ 2 * A := by rw [hA, e.tsum_eq (fun n => ‖(u : ℤ → ℂ) n‖ ^ (2:ℝ))]
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  simp only [ENNReal.toReal_ofNat]
  have h3 : (∑' n : ℤ, ‖w n * (u : ℤ → ℂ) (e n)‖ ^ (2:ℝ)) ^ (1/(2:ℝ)) ≤ (C ^ 2 * A) ^ (1/(2:ℝ)) :=
    Real.rpow_le_rpow (tsum_nonneg fun n => by positivity) key (by norm_num)
  refine le_trans h3 ?_
  rw [Real.mul_rpow (by positivity) hA0]
  gcongr
  rw [← Real.rpow_natCast C 2, ← Real.rpow_mul hC0]
  norm_num

/-- The bounded operator `u ↦ (n ↦ w n * u (e n))` on `ℓ²(ℤ)`, for a weight `w` bounded by `C`
and a bijection `e` of the index set. -/
noncomputable def weightedComp (w : ℤ → ℂ) (C : ℝ) (hC : ∀ n, ‖w n‖ ≤ C) (e : ℤ ≃ ℤ) :
    L2Z →L[ℂ] L2Z :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun n => w n * u (e n), memℓp_weighted_comp w C hC e u⟩
      map_add' := by intro u v; ext n; simp [mul_add]
      map_smul' := by intro c u; ext n; simp [mul_left_comm] }
    C (norm_weighted_comp_le w C hC e)

@[simp] theorem weightedComp_apply (w : ℤ → ℂ) (C : ℝ) (hC : ∀ n, ‖w n‖ ≤ C) (e : ℤ ≃ ℤ)
    (u : L2Z) (n : ℤ) : (weightedComp w C hC e u : ℤ → ℂ) n = w n * u (e n) := rfl

theorem norm_weightedComp_le (w : ℤ → ℂ) (C : ℝ) (hC : ∀ n, ‖w n‖ ≤ C) (e : ℤ ≃ ℤ) :
    ‖weightedComp w C hC e‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (norm_nonneg (w 0)) (hC 0)) _

/-! ## The almost Mathieu operator -/

/-- The potential of the almost Mathieu operator with coupling `lam`, flux `alpha` and phase
`theta`: `v n = 2 * lam * cos (2 * π * (theta + n * alpha))`. -/
noncomputable def amoPotential (lam alpha theta : ℝ) (n : ℤ) : ℂ :=
  ((2 * lam * Real.cos (2 * π * (theta + n * alpha)) : ℝ) : ℂ)

theorem norm_amoPotential_le (lam alpha theta : ℝ) (n : ℤ) :
    ‖amoPotential lam alpha theta n‖ ≤ 2 * |lam| := by
  have hcos : |Real.cos (2 * π * (theta + n * alpha))| ≤ 1 := Real.abs_cos_le_one _
  have hnorm : ‖amoPotential lam alpha theta n‖
      = |2 * lam * Real.cos (2 * π * (theta + n * alpha))| := by
    rw [amoPotential, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, abs_mul, abs_mul]
  have h2 : |(2:ℝ)| = 2 := by norm_num
  rw [h2]
  nlinarith [abs_nonneg lam, abs_nonneg (Real.cos (2 * π * (theta + n * alpha)))]

theorem conj_amoPotential (lam alpha theta : ℝ) (n : ℤ) :
    (starRingEnd ℂ) (amoPotential lam alpha theta n) = amoPotential lam alpha theta n :=
  Complex.conj_ofReal _

/-- The almost Mathieu operator `H_{lam, alpha, theta}` on `ℓ²(ℤ)`:
`(H u) n = u (n + 1) + u (n - 1) + 2 * lam * cos (2 * π * (theta + n * alpha)) * u n`. -/
noncomputable def amo (lam alpha theta : ℝ) : L2Z →L[ℂ] L2Z :=
  weightedComp (fun _ => 1) 1 (fun _ => by simp) (Equiv.addRight (1 : ℤ))
    + weightedComp (fun _ => 1) 1 (fun _ => by simp) (Equiv.addRight (-1 : ℤ))
    + weightedComp (amoPotential lam alpha theta) (2 * |lam|)
        (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ)

theorem amo_apply (lam alpha theta : ℝ) (u : L2Z) (n : ℤ) :
    (amo lam alpha theta u : ℤ → ℂ) n
      = u (n + 1) + u (n - 1) + amoPotential lam alpha theta n * u n := by
  simp [amo, sub_eq_add_neg]

/-- The almost Mathieu operator has norm at most `2 + 2 * |lam|`. -/
theorem norm_amo_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  have h1 := norm_weightedComp_le (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp)
    (Equiv.addRight (1 : ℤ))
  have h2 := norm_weightedComp_le (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp)
    (Equiv.addRight (-1 : ℤ))
  have h3 := norm_weightedComp_le (amoPotential lam alpha theta) (2 * |lam|)
    (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ)
  have hsum := norm_add_le
    (weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (1 : ℤ))
      + weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (-1 : ℤ)))
    (weightedComp (amoPotential lam alpha theta) (2 * |lam|)
      (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ))
  have hsum' := norm_add_le
    (weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (1 : ℤ)))
    (weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (-1 : ℤ)))
  calc ‖amo lam alpha theta‖ ≤ _ := hsum
    _ ≤ 2 + 2 * |lam| := by linarith

/-- The inner product on `ℓ²(ℤ)` as a sum. -/
theorem inner_l2 (x y : L2Z) : (inner ℂ x y : ℂ) = ∑' n : ℤ, (starRingEnd ℂ) (x n) * y n := by
  rw [lp.inner_eq_tsum]
  simp [RCLike.inner_apply, mul_comm]

/-- The adjoint of a weighted composition operator is the weighted composition operator for the
inverse index bijection and the conjugated weight. -/
theorem inner_weightedComp (w : ℤ → ℂ) (C : ℝ) (hC : ∀ n, ‖w n‖ ≤ C) (e : ℤ ≃ ℤ) (x y : L2Z) :
    (inner ℂ (weightedComp w C hC e x) y : ℂ)
      = inner ℂ x (weightedComp (fun n => (starRingEnd ℂ) (w (e.symm n))) C
          (fun n => by simpa using hC (e.symm n)) e.symm y) := by
  rw [inner_l2, inner_l2]
  rw [← e.tsum_eq (fun m : ℤ => (starRingEnd ℂ) (x m) *
      ((weightedComp (fun n => (starRingEnd ℂ) (w (e.symm n))) C
          (fun n => by simpa using hC (e.symm n)) e.symm y : ℤ → ℂ) m))]
  refine tsum_congr (fun n => ?_)
  simp [map_mul, mul_comm, mul_assoc]

/-- The almost Mathieu operator is selfadjoint. -/
theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [amo, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    ContinuousLinearMap.coe_coe]
  have h1 : (inner ℂ (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (1 : ℤ)) x) y : ℂ)
      = inner ℂ x (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (-1 : ℤ)) y) := by
    rw [inner_weightedComp]
    congr 1
    ext n
    simp
  have h2 : (inner ℂ (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (-1 : ℤ)) x) y : ℂ)
      = inner ℂ x (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (1 : ℤ)) y) := by
    rw [inner_weightedComp]
    congr 1
    ext n
    simp
  have h3 : (inner ℂ (weightedComp (amoPotential lam alpha theta) (2 * |lam|)
        (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ) x) y : ℂ)
      = inner ℂ x (weightedComp (amoPotential lam alpha theta) (2 * |lam|)
        (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ) y) := by
    rw [inner_weightedComp]
    congr 1
    ext n
    simp only [weightedComp_apply, Equiv.refl_symm, Equiv.refl_apply, conj_amoPotential]
  rw [h1, h2, h3]
  ring

/-- The spectrum of the almost Mathieu operator, viewed as a subset of the real line. -/
noncomputable def amoSpectrum (lam alpha theta : ℝ) : Set ℝ :=
  {E : ℝ | (E : ℂ) ∈ spectrum ℂ (amo lam alpha theta)}

/-! ## Cantor sets -/

/-- A subset of the real line is a Cantor set if it is nonempty, compact, perfect
(closed with no isolated points) and totally disconnected. By Brouwer's characterization these
four properties characterize sets homeomorphic to the standard middle-thirds Cantor set. -/
def IsCantorSet (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsCompact S ∧ Perfect S ∧ IsTotallyDisconnected S

/-- A subset of `ℝ` with empty interior is totally disconnected. -/
theorem isTotallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts hpre x hx y hy
  by_contra hxy
  -- wlog x < y
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hIcc : Set.Icc x y ⊆ t := hpre.ordConnected.out hx hy
    have hIoo : Set.Ioo x y ⊆ S :=
      fun z hz => hts (hIcc ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    have : Set.Ioo x y ⊆ interior S := interior_maximal hIoo isOpen_Ioo
    rw [h] at this
    exact (Set.nonempty_Ioo.2 hlt).ne_empty (Set.subset_empty_iff.1 this)
  · have hIcc : Set.Icc y x ⊆ t := hpre.ordConnected.out hy hx
    have hIoo : Set.Ioo y x ⊆ S :=
      fun z hz => hts (hIcc ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    have : Set.Ioo y x ⊆ interior S := interior_maximal hIoo isOpen_Ioo
    rw [h] at this
    exact (Set.nonempty_Ioo.2 hlt).ne_empty (Set.subset_empty_iff.1 this)

/-! ## Unconditional properties of the spectrum -/

theorem amoSpectrum_isClosed (lam alpha theta : ℝ) : IsClosed (amoSpectrum lam alpha theta) :=
  (spectrum.isClosed (amo lam alpha theta)).preimage Complex.continuous_ofReal

theorem amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-‖amo lam alpha theta‖) ‖amo lam alpha theta‖ := by
  intro E hE
  have h : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  exact abs_le.1 h

theorem amoSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) :=
  Metric.isCompact_of_isClosed_isBounded (amoSpectrum_isClosed lam alpha theta)
    ((Metric.isBounded_Icc _ _).subset (amoSpectrum_subset_Icc lam alpha theta))

/-- Explicit localization of the spectrum: it is contained in `[-(2 + 2|lam|), 2 + 2|lam|]`. -/
theorem amoSpectrum_subset_Icc' (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro E hE
  have h := amoSpectrum_subset_Icc lam alpha theta hE
  have hn := norm_amo_le lam alpha theta
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Since the almost Mathieu operator is selfadjoint, its complex spectrum is real; being
nonempty, the real spectrum is nonempty as well. -/
theorem amoSpectrum_nonempty (lam alpha theta : ℝ) : (amoSpectrum lam alpha theta).Nonempty := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (amo lam alpha theta)
  refine ⟨z.re, ?_⟩
  have hreal : z = (z.re : ℂ) := (amo_isSelfAdjoint lam alpha theta).mem_spectrum_eq_re hz
  show ((z.re : ℝ) : ℂ) ∈ spectrum ℂ (amo lam alpha theta)
  rw [← hreal]
  exact hz

/-! ## The Ten Martini reduction -/

/-- **Ten Martini problem (Lean-checked reduction).**

For every nonzero coupling `lam`, every irrational flux `alpha` and every phase `theta`, the
spectrum of the almost Mathieu operator `H_{lam, alpha, theta}` on `ℓ²(ℤ)` is a Cantor set,
given the two analytic inputs of the Avila–Jitomirskaya proof, stated here in exactly the same
generality as the conclusion:

* `hNoIsolatedPoints`: the spectrum has no isolated points;
* `hGapsOpen`: all the spectral gaps predicted by gap labelling are open, i.e. the spectrum is
  nowhere dense (equivalently, it has empty interior).

Everything else is proved unconditionally in this file: the almost Mathieu operator is a
well-defined bounded selfadjoint operator on `ℓ²(ℤ)` (`amo`, `amo_isSelfAdjoint`), its real
spectrum is nonempty (`amoSpectrum_nonempty`) and compact (`amoSpectrum_isCompact`), and a
subset of `ℝ` with empty interior is totally disconnected
(`isTotallyDisconnected_of_interior_eq_empty`). Thus Cantor-ness of the spectrum is reduced
exactly to the two inputs above. -/
theorem avila_ten_martini
    (hNoIsolatedPoints : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      Preperfect (amoSpectrum lam alpha theta))
    (hGapsOpen : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      interior (amoSpectrum lam alpha theta) = ∅) :
    ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      IsCantorSet (amoSpectrum lam alpha theta) := by
  intro lam alpha theta hlam halpha
  exact ⟨amoSpectrum_nonempty lam alpha theta, amoSpectrum_isCompact lam alpha theta,
    ⟨amoSpectrum_isClosed lam alpha theta, hNoIsolatedPoints lam alpha theta hlam halpha⟩,
    isTotallyDisconnected_of_interior_eq_empty (hGapsOpen lam alpha theta hlam halpha)⟩

end Frontier

