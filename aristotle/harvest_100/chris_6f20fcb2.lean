/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/
noncomputable def ltConst (Kc : ℝ) : ℝ := (2 / 5) * (3 / (5 * Kc)) ^ (3 / 2 : ℝ)

lemma ltConst_nonneg {Kc : ℝ} (hKc : 0 < Kc) : 0 ≤ ltConst Kc := by
  unfold ltConst
  positivity

/-- Pointwise minimization: for `a, t ≥ 0` and `Kc > 0`,
`t * a ≤ Kc * a ^ (5/3) + ltConst Kc * t ^ (5/2)`.
This is the exact value of `min_{a ≥ 0} (Kc a^{5/3} - t a)`, obtained from Young's
inequality with the conjugate exponents `5/3` and `5/2`. -/
lemma mul_le_rpow_five_thirds_add {Kc t a : ℝ} (hKc : 0 < Kc) (ht : 0 ≤ t) (ha : 0 ≤ a) :
    t * a ≤ Kc * a ^ (5 / 3 : ℝ) + ltConst Kc * t ^ (5 / 2 : ℝ) := by
  have hconj : Real.HolderConjugate (5 / 3 : ℝ) (5 / 2) := by constructor <;> norm_num
  set lam : ℝ := (5 * Kc / 3) ^ (3 / 5 : ℝ) with hlam
  have hlampos : 0 < lam := Real.rpow_pos_of_pos (by linarith) _
  have h := Real.young_inequality_of_nonneg (a := lam * a) (b := t / lam)
    (by positivity) (by positivity) hconj
  have hmul : (lam * a) * (t / lam) = t * a := by field_simp
  rw [hmul] at h
  refine h.trans_eq ?_
  have h1 : (lam * a) ^ (5 / 3 : ℝ) = lam ^ (5 / 3 : ℝ) * a ^ (5 / 3 : ℝ) :=
    Real.mul_rpow hlampos.le ha
  have h2 : lam ^ (5 / 3 : ℝ) = 5 * Kc / 3 := by
    rw [hlam, ← Real.rpow_mul (by linarith)]
    norm_num
  have h3 : (t / lam) ^ (5 / 2 : ℝ) = t ^ (5 / 2 : ℝ) / lam ^ (5 / 2 : ℝ) :=
    Real.div_rpow ht hlampos.le _
  have h4 : lam ^ (5 / 2 : ℝ) = (5 * Kc / 3) ^ (3 / 2 : ℝ) := by
    rw [hlam, ← Real.rpow_mul (by linarith)]
    norm_num
  have h5 : (3 / (5 * Kc)) ^ (3 / 2 : ℝ) = ((5 * Kc / 3) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [show (3 : ℝ) / (5 * Kc) = (5 * Kc / 3)⁻¹ by field_simp, Real.inv_rpow (by positivity)]
  have h6 : (0 : ℝ) < (5 * Kc / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [ltConst, h1, h2, h3, h4, h5]
  field_simp

/-- **Sharpness**: equality holds in `mul_le_rpow_five_thirds_add` at `a = (3t/(5Kc))^{3/2}`,
so `ltConst Kc` is the optimal constant in that pointwise bound. -/
lemma mul_le_rpow_five_thirds_add_sharp {Kc t : ℝ} (hKc : 0 < Kc) (ht : 0 ≤ t) :
    ∃ a : ℝ, 0 ≤ a ∧ t * a = Kc * a ^ (5 / 3 : ℝ) + ltConst Kc * t ^ (5 / 2 : ℝ) := by
  refine ⟨(3 * t / (5 * Kc)) ^ (3 / 2 : ℝ), Real.rpow_nonneg (by positivity) _, ?_⟩
  rcases eq_or_lt_of_le ht with h | ht'
  · rw [← h]
    norm_num
  set s : ℝ := 3 * t / (5 * Kc) with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hts : t = (5 * Kc / 3) * s := by rw [hs]; field_simp
  have e1 : (s ^ (3 / 2 : ℝ)) ^ (5 / 3 : ℝ) = s ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_mul hspos.le]; norm_num
  have e2 : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hspos, Real.rpow_one]
  have e3 : t ^ (5 / 2 : ℝ) = (5 * Kc / 3) ^ (5 / 2 : ℝ) * s ^ (5 / 2 : ℝ) := by
    rw [hts]; exact Real.mul_rpow (by positivity) hspos.le
  have e4 : (2 / 5 : ℝ) * (3 / (5 * Kc)) ^ (3 / 2 : ℝ) * (5 * Kc / 3) ^ (5 / 2 : ℝ)
      = (2 / 5) * (5 * Kc / 3) := by
    have h : (3 / (5 * Kc) : ℝ) = ((5 * Kc / 3))⁻¹ := by field_simp
    rw [h, Real.inv_rpow (by positivity)]
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
    field_simp
  rw [ltConst, e1, e3, e2]
  linear_combination (s ^ (3 / 2 : ℝ)) * hts - (s ^ (3 / 2 : ℝ) * s) * e4

/-! ## Abstract energy lower bound on a measure space -/

/-- Lieb–Thirring type kinetic energy bound: the kinetic energy `T` dominates
`Kc * ∫ ρ ^ (5/3)`. -/
def LTKineticBound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (Kc T : ℝ) (ρ : α → ℝ) : Prop :=
  Kc * ∫ x, (ρ x) ^ (5 / 3 : ℝ) ∂μ ≤ T

/-- Bound on the (attractive) potential energy by a one-body potential `W`:
`V ≥ - b ∫ W ρ`. -/
def AttractionBound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b V : ℝ) (W ρ : α → ℝ) : Prop :=
  -(b * ∫ x, W x * ρ x ∂μ) ≤ V

/-- **Core stability estimate.** If the kinetic energy obeys a Lieb–Thirring bound and the
potential energy is bounded below by `-b ∫ W ρ`, then the total energy is bounded below by
`- ltConst Kc * b ^ (5/2) * ∫ W ^ (5/2)`, independently of the density `ρ`
(in particular, independently of the particle number). -/
theorem energy_lower_bound_of_LT {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {Kc b T V : ℝ} {ρ W : α → ℝ}
    (hKc : 0 < Kc) (hb : 0 ≤ b)
    (hρ : ∀ x, 0 ≤ ρ x) (hW : ∀ x, 0 ≤ W x)
    (hρint : Integrable (fun x => (ρ x) ^ (5 / 3 : ℝ)) μ)
    (hWρint : Integrable (fun x => W x * ρ x) μ)
    (hWint : Integrable (fun x => (W x) ^ (5 / 2 : ℝ)) μ)
    (hT : LTKineticBound μ Kc T ρ)
    (hV : AttractionBound μ b V W ρ) :
    -(ltConst Kc * b ^ (5 / 2 : ℝ) * ∫ x, (W x) ^ (5 / 2 : ℝ) ∂μ) ≤ T + V := by
  rw [LTKineticBound] at hT
  rw [AttractionBound] at hV
  have hpt : ∀ x, b * (W x * ρ x)
      ≤ Kc * (ρ x) ^ (5 / 3 : ℝ) + ltConst Kc * b ^ (5 / 2 : ℝ) * (W x) ^ (5 / 2 : ℝ) := by
    intro x
    have h := mul_le_rpow_five_thirds_add (Kc := Kc) (t := b * W x) (a := ρ x)
      hKc (mul_nonneg hb (hW x)) (hρ x)
    rw [Real.mul_rpow hb (hW x), ← mul_assoc] at h
    calc b * (W x * ρ x) = (b * W x) * ρ x := by ring
      _ ≤ _ := h
  have hint2 : Integrable (fun x => Kc * (ρ x) ^ (5 / 3 : ℝ)
      + ltConst Kc * b ^ (5 / 2 : ℝ) * (W x) ^ (5 / 2 : ℝ)) μ :=
    (hρint.const_mul Kc).add (hWint.const_mul _)
  have hmono := integral_mono (hWρint.const_mul b) hint2 hpt
  rw [integral_add (hρint.const_mul Kc) (hWint.const_mul _)] at hmono
  simp only [integral_const_mul] at hmono
  linarith

/-! ## The many-body setting in `ℝ³` -/

/-- Configuration space of one particle. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- The squared modulus of the gradient, `|∇ψ(x)|² = ∑ⱼ |∂ⱼψ(x)|²`. -/
noncomputable def gradSqNorm (ψ : Space → ℂ) (x : Space) : ℝ :=
  ∑ j : Fin 3, ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2

/-- Kinetic energy `∫ |∇ψ|²` of a one-particle wave function. -/
noncomputable def kineticEnergy (ψ : Space → ℂ) : ℝ :=
  ∫ x, gradSqNorm ψ x

/-- One-particle density `ρ(x) = ∑ᵢ |ψᵢ(x)|²` of a Slater-type family. -/
noncomputable def density {N : ℕ} (ψ : Fin N → Space → ℂ) : Space → ℝ :=
  fun x => ∑ i, ‖ψ i x‖ ^ 2

lemma density_nonneg {N : ℕ} (ψ : Fin N → Space → ℂ) (x : Space) : 0 ≤ density ψ x :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Orthonormality of a finite family of one-particle wave functions in `L²(ℝ³)`. -/
def L2Orthonormal {N : ℕ} (ψ : Fin N → Space → ℂ) : Prop :=
  ∀ i j, (∫ x, (starRingEnd ℂ) (ψ i x) * ψ j x) = if i = j then 1 else 0

/-- Admissible (finite kinetic energy, differentiable, orthonormal) families of one-particle
wave functions. -/
def Admissible {N : ℕ} (ψ : Fin N → Space → ℂ) : Prop :=
  (∀ i, Differentiable ℝ (ψ i)) ∧ (∀ i, Integrable (gradSqNorm (ψ i))) ∧ L2Orthonormal ψ

/-- **The Lieb–Thirring kinetic energy inequality** with constant `Kc`: for every finite
orthonormal family of (differentiable) one-particle wave functions, the total kinetic
energy dominates `Kc ∫ ρ^{5/3}`, where `ρ` is the associated one-particle density.
This is the fermionic (Pauli-principle) strengthening of the Sobolev inequality; it is the
deep analytic input of the Lieb–Thirring proof of stability of matter, and is taken here as
a hypothesis. -/
def LiebThirringKineticInequality (Kc : ℝ) : Prop :=
  ∀ (N : ℕ) (ψ : Fin N → Space → ℂ), Admissible ψ →
    Kc * ∫ x, (density ψ x) ^ (5 / 3 : ℝ) ≤ ∑ i, kineticEnergy (ψ i)

/-- **Stability of matter, reduced to the Lieb–Thirring inequality.**

For a system of `N` fermions described by an orthonormal family `ψ` of one-particle wave
functions, whose interaction energy `V` with the nuclei (and among themselves) is bounded
below by `- b ∫ W ρ` for a nonnegative one-body potential `W` with `W ^ (5/2)` integrable
(this is the content of the electrostatic/Baxter inequality, with `W` the inverse distance
to the nearest nucleus suitably localized), the total energy satisfies the uniform lower
bound

`E = T + V ≥ - ltConst Kc * b ^ (5/2) * ∫ W ^ (5/2)`,

whose right-hand side does not depend on the number `N` of particles. Combined with a bound
`∫ W ^ (5/2) ≤ A * K` for `K` nuclei, this gives the linear-in-particle-number lower bound
that constitutes stability of matter. -/
theorem lieb_thirring_stability
    {Kc b V : ℝ} {N : ℕ} {ψ : Fin N → Space → ℂ} {W : Space → ℝ}
    (hKc : 0 < Kc) (hb : 0 ≤ b)
    (hLT : LiebThirringKineticInequality Kc)
    (hadm : Admissible ψ)
    (hW : ∀ x, 0 ≤ W x)
    (hρint : Integrable (fun x => (density ψ x) ^ (5 / 3 : ℝ)))
    (hWρint : Integrable (fun x => W x * density ψ x))
    (hWint : Integrable (fun x => (W x) ^ (5 / 2 : ℝ)))
    (hV : -(b * ∫ x, W x * density ψ x) ≤ V) :
    -(ltConst Kc * b ^ (5 / 2 : ℝ) * ∫ x, (W x) ^ (5 / 2 : ℝ))
      ≤ (∑ i, kineticEnergy (ψ i)) + V :=
  energy_lower_bound_of_LT (μ := volume) hKc hb (density_nonneg ψ) hW hρint hWρint hWint
    (hLT N ψ hadm) hV

/-! ## The base case `N = 1` of the Lieb–Thirring kinetic inequality

For a single particle the Lieb–Thirring inequality reduces to the Sobolev inequality
`‖ψ‖_6 ≤ C ‖∇ψ‖_2` combined with the Hölder interpolation
`‖ψ‖_{10/3}^{10/3} ≤ ‖ψ‖_2^{4/3} ‖ψ‖_6^2`. We prove this base case unconditionally,
for `C¹` wave functions with compact support. -/

/-- The operator norm of the derivative is dominated by the Euclidean length of the
gradient. -/
lemma opNorm_sq_le_gradSqNorm (ψ : Space → ℂ) (x : Space) :
    ‖fderiv ℝ ψ x‖ ^ 2 ≤ gradSqNorm ψ x := by
  set L : Space →L[ℝ] ℂ := fderiv ℝ ψ x with hL
  set S : ℝ := ∑ j : Fin 3, ‖L (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ‖L‖ ≤ Real.sqrt S := by
    refine L.opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
    have hx : x = ∑ j : Fin 3, (x j) • (EuclideanSpace.single j (1 : ℝ)) := by
      ext i; simp [Pi.single_apply]
    have h1 : ‖L x‖ ≤ ∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖ := by
      calc ‖L x‖ = ‖∑ j : Fin 3, (x j) • L (EuclideanSpace.single j (1 : ℝ))‖ := by
            conv_lhs => rw [hx]
            simp [map_sum]
        _ ≤ ∑ j : Fin 3, ‖(x j) • L (EuclideanSpace.single j (1 : ℝ))‖ := norm_sum_le _ _
        _ = _ := by simp
    have hsum0 : 0 ≤ ∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖ :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h2 : (∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
        ≤ (∑ j : Fin 3, |x j| ^ 2) * S :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hnx : ‖x‖ = Real.sqrt (∑ j : Fin 3, |x j| ^ 2) := by
      rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs]
    have h3 : (∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖)
        ≤ Real.sqrt ((∑ j : Fin 3, |x j| ^ 2) * S) := by
      have h4 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq hsum0] at h4
    calc ‖L x‖ ≤ _ := h1
      _ ≤ Real.sqrt ((∑ j : Fin 3, |x j| ^ 2) * S) := h3
      _ = Real.sqrt S * ‖x‖ := by
          rw [hnx, Real.sqrt_mul (by positivity)]; ring
  have hgrad : gradSqNorm ψ x = S := rfl
  rw [hgrad]
  have hsq := Real.sq_sqrt hS0
  nlinarith [norm_nonneg L, Real.sqrt_nonneg S]

/-- The constant in the Sobolev inequality `‖ψ‖_6 ≤ sobolevConst ‖Dψ‖_2` on `ℝ³`. -/
noncomputable def sobolevConst : ℝ :=
  (MeasureTheory.SNormLESNormFDerivOfEqConst ℂ (volume : Measure Space) 2 : NNReal)

lemma sobolevConst_nonneg : 0 ≤ sobolevConst :=
  (MeasureTheory.SNormLESNormFDerivOfEqConst ℂ (volume : Measure Space) 2).2

/-- The Sobolev inequality on `ℝ³` in the form of Bochner integrals. -/
lemma sobolev_six_le (ψ : Space → ℂ) (h1 : ContDiff ℝ 1 ψ) (h2 : HasCompactSupport ψ) :
    (∫ x, ‖ψ x‖ ^ 6) ^ (1 / 6 : ℝ)
      ≤ sobolevConst * (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hmain := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℂ) (E := Space)
    (volume : Measure Space) h1 h2 (p := 2) (p' := 6) (by norm_num) (by simp) (by simp; norm_num)
  simp only [ENNReal.coe_ofNat] at hmain
  have hψ : MemLp ψ 6 (volume : Measure Space) := h1.continuous.memLp_of_hasCompactSupport h2
  have hcd : Continuous (fderiv ℝ ψ) := h1.continuous_fderiv (by norm_num)
  have hd : MemLp (fderiv ℝ ψ) 2 (volume : Measure Space) :=
    hcd.memLp_of_hasCompactSupport (h2.fderiv (𝕜 := ℝ))
  rw [hψ.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      hd.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hmain
  norm_num at hmain
  rw [show ((MeasureTheory.SNormLESNormFDerivOfEqConst ℂ (volume : Measure Space) 2 : NNReal)
        : ENNReal) = ENNReal.ofReal sobolevConst from ENNReal.ofReal_coe_nnreal.symm,
      ← ENNReal.ofReal_mul sobolevConst_nonneg] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg sobolevConst_nonneg
    (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _))).mp hmain

/-- Hölder interpolation of the `L^{10/3}` norm between `L²` and `L⁶`. -/
lemma holder_interp_ten_thirds (ψ : Space → ℂ) (hc : Continuous ψ) (h2 : HasCompactSupport ψ) :
    ∫ x, ‖ψ x‖ ^ (10 / 3 : ℝ)
      ≤ (∫ x, ‖ψ x‖ ^ 2) ^ (2 / 3 : ℝ) * (∫ x, ‖ψ x‖ ^ 6) ^ (1 / 3 : ℝ) := by
  have hconj : (3 / 2 : ℝ).HolderConjugate 3 := by constructor <;> norm_num
  set f : Space → ℝ := fun x => ‖ψ x‖ ^ (4 / 3 : ℝ) with hf
  set g : Space → ℝ := fun x => ‖ψ x‖ ^ 2 with hg
  have hfc : Continuous f := (hc.norm).rpow_const (fun _ => Or.inr (by norm_num))
  have hgc : Continuous g := (hc.norm).pow 2
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.comp_left (g := fun t : ℝ => t ^ (4 / 3 : ℝ)) (h2.norm)
    simp [Real.zero_rpow]
  have hgs : HasCompactSupport g := by
    apply HasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (h2.norm)
    simp
  have hfm : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Space) :=
    hfc.memLp_of_hasCompactSupport hfs
  have hgm : MemLp g (ENNReal.ofReal (3 : ℝ)) (volume : Measure Space) :=
    hgc.memLp_of_hasCompactSupport hgs
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hconj hfm hgm
  have e0 : ∀ a : Space, ‖f a‖ * ‖g a‖ = ‖ψ a‖ ^ (10 / 3 : ℝ) := by
    intro a
    have hn : (0 : ℝ) ≤ ‖ψ a‖ := norm_nonneg _
    rw [hf, hg]
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ψ a‖ ^ 2)]
    rw [show ((10 : ℝ) / 3) = 4 / 3 + 2 by norm_num, Real.rpow_add' hn (by norm_num)]
    norm_num
  have e1 : ∀ a : Space, ‖f a‖ ^ (3 / 2 : ℝ) = ‖ψ a‖ ^ 2 := by
    intro a
    have hn : (0 : ℝ) ≤ ‖ψ a‖ := norm_nonneg _
    rw [hf]
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn _)]
    rw [← Real.rpow_mul hn]
    norm_num
  have e2 : ∀ a : Space, ‖g a‖ ^ (3 : ℝ) = ‖ψ a‖ ^ 6 := by
    intro a
    rw [hg]
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ψ a‖ ^ 2)]
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  simp only [e0, e1, e2] at h
  convert h using 3
  norm_num

/-- **The base case `N = 1` of the Lieb–Thirring kinetic energy inequality.**
For a single normalized `C¹` wave function with compact support,
`∫ ρ^{5/3} ≤ sobolevConst² · ∫ |∇ψ|²`, where `ρ = |ψ|²`. This is proved unconditionally
from the Sobolev inequality and Hölder interpolation. -/
theorem lieb_thirring_one_particle (ψ : Space → ℂ) (h1 : ContDiff ℝ 1 ψ)
    (hcs : HasCompactSupport ψ) (hnorm : (∫ x, ‖ψ x‖ ^ 2) = 1) :
    (∫ x, (density (fun _ : Fin 1 => ψ) x) ^ (5 / 3 : ℝ)) ≤ sobolevConst ^ 2 * kineticEnergy ψ := by
  have hcd : Continuous (fderiv ℝ ψ) := h1.continuous_fderiv (by norm_num)
  have hfds : HasCompactSupport (fderiv ℝ ψ) := hcs.fderiv (𝕜 := ℝ)
  -- densities
  have hdens : ∀ x, (density (fun _ : Fin 1 => ψ) x) ^ (5 / 3 : ℝ) = ‖ψ x‖ ^ (10 / 3 : ℝ) := by
    intro x
    have hn : (0 : ℝ) ≤ ‖ψ x‖ := norm_nonneg _
    simp only [density, Finset.univ_unique, Finset.sum_singleton]
    rw [← Real.rpow_natCast (‖ψ x‖) 2, ← Real.rpow_mul hn]
    norm_num
  -- kinetic energy dominates the operator-norm integral
  have hgc : Continuous (gradSqNorm ψ) := by
    refine continuous_finset_sum _ fun j _ => ?_
    exact ((hcd.clm_apply continuous_const).norm).pow 2
  have hgs : HasCompactSupport (gradSqNorm ψ) := by
    apply HasCompactSupport.comp_left
      (g := fun L : Space →L[ℝ] ℂ => ∑ j : Fin 3, ‖L (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) hfds
    simp
  have hopc : Continuous (fun x => ‖fderiv ℝ ψ x‖ ^ 2) := (hcd.norm).pow 2
  have hops : HasCompactSupport (fun x => ‖fderiv ℝ ψ x‖ ^ 2) := by
    apply HasCompactSupport.comp_left (g := fun L : Space →L[ℝ] ℂ => ‖L‖ ^ 2) hfds
    simp
  have hTle : (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) ≤ kineticEnergy ψ :=
    integral_mono (hopc.integrable_of_hasCompactSupport hops)
      (hgc.integrable_of_hasCompactSupport hgs) (opNorm_sq_le_gradSqNorm ψ)
  -- Sobolev + Hölder
  set B : ℝ := ∫ x, ‖ψ x‖ ^ 6 with hB
  set T : ℝ := ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 with hT
  have hB0 : 0 ≤ B := integral_nonneg fun x => by positivity
  have hT0 : 0 ≤ T := integral_nonneg fun x => by positivity
  have hsob := sobolev_six_le ψ h1 hcs
  have hsq : B ^ (1 / 3 : ℝ) ≤ sobolevConst ^ 2 * T := by
    have h6 : (0 : ℝ) ≤ B ^ (1 / 6 : ℝ) := Real.rpow_nonneg hB0 _
    have hmul := mul_self_le_mul_self h6 hsob
    have e1 : B ^ (1 / 6 : ℝ) * B ^ (1 / 6 : ℝ) = B ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add' hB0 (by norm_num)]
      norm_num
    have e2 : (sobolevConst * T ^ (1 / 2 : ℝ)) * (sobolevConst * T ^ (1 / 2 : ℝ))
        = sobolevConst ^ 2 * T := by
      have : T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) = T := by
        rw [← Real.rpow_add' hT0 (by norm_num)]
        norm_num
      nlinarith [this]
    rwa [e1, e2] at hmul
  have hhol := holder_interp_ten_thirds ψ h1.continuous hcs
  rw [hnorm] at hhol
  simp only [Real.one_rpow, one_mul] at hhol
  simp only [hdens]
  calc (∫ x, ‖ψ x‖ ^ (10 / 3 : ℝ)) ≤ B ^ (1 / 3 : ℝ) := hhol
    _ ≤ sobolevConst ^ 2 * T := hsq
    _ ≤ sobolevConst ^ 2 * kineticEnergy ψ := by
        have : (0 : ℝ) ≤ sobolevConst ^ 2 := by positivity
        nlinarith [hTle]

lemma kineticEnergy_nonneg (ψ : Space → ℂ) : 0 ≤ kineticEnergy ψ :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by positivity

/-- The base case in the normalized form of the Lieb–Thirring inequality: any constant `Kc`
with `Kc * sobolevConst ^ 2 ≤ 1` works for a single particle. -/
theorem lieb_thirring_one_particle_const {Kc : ℝ} (hKc0 : 0 ≤ Kc)
    (hKc : Kc * sobolevConst ^ 2 ≤ 1) (ψ : Space → ℂ) (h1 : ContDiff ℝ 1 ψ)
    (hcs : HasCompactSupport ψ) (hnorm : (∫ x, ‖ψ x‖ ^ 2) = 1) :
    Kc * ∫ x, (density (fun _ : Fin 1 => ψ) x) ^ (5 / 3 : ℝ) ≤ kineticEnergy ψ := by
  have h := lieb_thirring_one_particle ψ h1 hcs hnorm
  have hk0 : 0 ≤ kineticEnergy ψ := kineticEnergy_nonneg ψ
  nlinarith

/-- **Extensivity (linear lower bound in the number of nuclei).** If the localized
one-body potential satisfies `∫ W ^ (5/2) ≤ A * K` where `K` is the number of nuclei,
then the energy is bounded below by a constant times `K`, uniformly in the number of
electrons. -/
theorem lieb_thirring_stability_linear
    {Kc b V A : ℝ} {K : ℕ} {N : ℕ} {ψ : Fin N → Space → ℂ} {W : Space → ℝ}
    (hKc : 0 < Kc) (hb : 0 ≤ b)
    (hLT : LiebThirringKineticInequality Kc)
    (hadm : Admissible ψ)
    (hW : ∀ x, 0 ≤ W x)
    (hρint : Integrable (fun x => (density ψ x) ^ (5 / 3 : ℝ)))
    (hWρint : Integrable (fun x => W x * density ψ x))
    (hWint : Integrable (fun x => (W x) ^ (5 / 2 : ℝ)))
    (hV : -(b * ∫ x, W x * density ψ x) ≤ V)
    (hA : (∫ x, (W x) ^ (5 / 2 : ℝ)) ≤ A * K) :
    -(ltConst Kc * b ^ (5 / 2 : ℝ) * A) * K ≤ (∑ i, kineticEnergy (ψ i)) + V := by
  have hC : 0 ≤ ltConst Kc * b ^ (5 / 2 : ℝ) :=
    mul_nonneg (ltConst_nonneg hKc) (Real.rpow_nonneg hb _)
  have h1 := lieb_thirring_stability hKc hb hLT hadm hW hρint hWρint hWint hV
  have h2 := mul_le_mul_of_nonneg_left hA hC
  linarith

end Frontier

