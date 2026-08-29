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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.FreeLaplacianPlancherel

open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv

/-- Euclidean space `ℝ^d`, the configuration space of the free Laplacian. -/
abbrev Eucl (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
noncomputable abbrev L2 (d : ℕ) := Lp (α := Eucl d) ℂ 2 volume

/-- A Schwartz function, viewed as an element of `L²(ℝ^d)`. The Schwartz space is the core
(dense domain) on which we consider the free Laplacian. -/
noncomputable def toL2 {d : ℕ} (f : 𝓢(Eucl d, ℂ)) : L2 d := f.toLp 2 volume

/-- The free Laplacian `-Δ`, acting on the Schwartz core, with values in `L²(ℝ^d)`. -/
noncomputable def freeLaplacian {d : ℕ} (f : 𝓢(Eucl d, ℂ)) : L2 d := toL2 (-(Δ f))

/-- The Fourier multiplier of the free Laplacian: `4 π² ‖ξ‖²`. -/
noncomputable def symbol {d : ℕ} (ξ : Eucl d) : ℝ := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

/-- The Fourier transform turns the Laplacian into multiplication by `-4 π² ‖ξ‖²`. -/
theorem fourier_laplacian_apply {d : ℕ} (f : 𝓢(Eucl d, ℂ)) (ξ : Eucl d) :
    𝓕 (Δ f) ξ = -(4 * (Real.pi : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2) * 𝓕 f ξ := by
  set b := stdOrthonormalBasis ℝ (Eucl d) with hb
  have hgrow : ∀ m : Eucl d, Function.HasTemperateGrowth (fun x : Eucl d => inner ℝ x m) :=
    fun m => ((innerSL ℝ).flip m).hasTemperateGrowth
  have key : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = -(4 * (Real.pi : ℂ) ^ 2 * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2) * 𝓕 f ξ := by
    intro i
    rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
    simp only [smulLeftCLM_apply (hgrow (b i)), SchwartzMap.smul_apply]
    simp only [Complex.real_smul, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [laplacian_eq_sum b]
  have hsum : 𝓕 (∑ i, ∂_{b i} (∂_{b i} f)) = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) := by simp
  rw [hsum]
  simp only [SchwartzMap.sum_apply, key]
  rw [← Finset.sum_mul]
  congr 1
  have h2 : ∑ i, ((inner ℝ ξ (b i) : ℝ)) ^ 2 = ‖ξ‖ ^ 2 := OrthonormalBasis.sum_sq_inner_left b ξ
  have h2' : ((‖ξ‖ : ℂ)) ^ 2 = ∑ i, (((inner ℝ ξ (b i) : ℝ) : ℂ)) ^ 2 := by
    rw [← Complex.ofReal_pow, ← h2]; push_cast; ring
  rw [h2', Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- On the Fourier side, `-Δ` becomes multiplication by the symbol `4 π² ‖ξ‖²`. -/
theorem fourier_freeLaplacian_apply {d : ℕ} (f : 𝓢(Eucl d, ℂ)) (ξ : Eucl d) :
    𝓕 (-(Δ f)) ξ = (symbol ξ : ℂ) * 𝓕 f ξ := by
  have h : 𝓕 (-(Δ f)) ξ = -(𝓕 (Δ f) ξ) := by simp
  rw [h, fourier_laplacian_apply, symbol]
  push_cast
  ring

/-- Plancherel: the `L²` inner product of two Schwartz functions computed on the Fourier side. -/
theorem inner_toL2_eq_integral {d : ℕ} (a b : 𝓢(Eucl d, ℂ)) :
    inner ℂ (toL2 a) (toL2 b) = ∫ ξ, (starRingEnd ℂ) (𝓕 a ξ) * 𝓕 b ξ := by
  have h1 : inner ℂ (toL2 a) (toL2 b) = ∫ x, inner ℂ (a x) (b x) := by
    rw [toL2, toL2, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [a.coeFn_toLp 2 (volume : Measure (Eucl d)),
      b.coeFn_toLp 2 (volume : Measure (Eucl d))] with x hx1 hx2
    rw [hx1, hx2]
  rw [h1, ← SchwartzMap.integral_inner_fourier_fourier a b]
  simp [RCLike.inner_apply, mul_comm]

/-- The Schwartz core is dense in `L²(ℝ^d)`. -/
theorem dense_core (d : ℕ) : Dense (Set.range (fun f : 𝓢(Eucl d, ℂ) => toL2 f)) := by
  have := SchwartzMap.denseRange_toLpCLM (E := Eucl d) (F := ℂ) (p := 2)
    (μ := (volume : Measure (Eucl d))) ENNReal.ofNat_ne_top
  simpa [DenseRange, toL2, SchwartzMap.toLpCLM_apply] using this

/-- The free Laplacian is symmetric on the Schwartz core. -/
theorem freeLaplacian_symmetric {d : ℕ} (f g : 𝓢(Eucl d, ℂ)) :
    inner ℂ (freeLaplacian f) (toL2 g) = inner ℂ (toL2 f) (freeLaplacian g) := by
  rw [freeLaplacian, freeLaplacian, inner_toL2_eq_integral, inner_toL2_eq_integral]
  refine congrArg _ (funext fun ξ => ?_)
  simp only [fourier_freeLaplacian_apply, map_mul, Complex.conj_ofReal]
  ring

theorem toL2_add {d : ℕ} (f g : 𝓢(Eucl d, ℂ)) : toL2 (f + g) = toL2 f + toL2 g := by
  simpa [toL2, SchwartzMap.toLpCLM_apply] using
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Eucl d))).map_add f g

theorem toL2_smul {d : ℕ} (c : ℂ) (f : 𝓢(Eucl d, ℂ)) : toL2 (c • f) = c • toL2 f := by
  show (c • f).toLp 2 volume = c • (f.toLp 2 volume)
  rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (f := c • f),
    ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (f := f), map_smul]

theorem laplacian_add {d : ℕ} (f g : 𝓢(Eucl d, ℂ)) : Δ (f + g) = Δ f + Δ g := by
  rw [← laplacianCLM_eq (𝕜 := ℂ), ← laplacianCLM_eq (𝕜 := ℂ) f, ← laplacianCLM_eq (𝕜 := ℂ) g,
    map_add]

theorem laplacian_smul {d : ℕ} (c : ℂ) (f : 𝓢(Eucl d, ℂ)) : Δ (c • f) = c • Δ f := by
  rw [← laplacianCLM_eq (𝕜 := ℂ), ← laplacianCLM_eq (𝕜 := ℂ) f, map_smul]

/-- The operator `-Δ + z` on the Schwartz core, as a linear map into `L²(ℝ^d)`. -/
noncomputable def shiftMap (d : ℕ) (z : ℂ) : 𝓢(Eucl d, ℂ) →ₗ[ℂ] L2 d where
  toFun f := freeLaplacian f + z • toL2 f
  map_add' f g := by
    simp only [freeLaplacian, laplacian_add, neg_add, toL2_add, smul_add]
    abel
  map_smul' c f := by
    simp only [freeLaplacian, laplacian_smul, RingHom.id_apply, smul_add]
    rw [← smul_neg, toL2_smul, toL2_smul, smul_comm]

theorem range_shiftMap (d : ℕ) (z : ℂ) :
    Set.range (fun f : 𝓢(Eucl d, ℂ) => freeLaplacian f + z • toL2 f)
      = ((LinearMap.range (shiftMap d z) : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  ext x
  simp [shiftMap, LinearMap.mem_range]

/-- Plancherel transfers the orthogonality relation `⟪(-Δ + z) f, u⟫ = 0` for all Schwartz `f`
into the statement that the locally integrable function `(4π²‖ξ‖² + conj z) ⋅ (𝓕u)` annihilates
every Schwartz function. -/
theorem integral_conj_mul_symbol_eq_zero {d : ℕ} (z : ℂ) (u : L2 d)
    (horth : ∀ f : 𝓢(Eucl d, ℂ), inner ℂ (freeLaplacian f + z • toL2 f) u = 0)
    (g : 𝓢(Eucl d, ℂ)) :
    ∫ ξ, (starRingEnd ℂ) (g ξ) *
      (((symbol ξ : ℂ) + (starRingEnd ℂ) z) * ((𝓕 u : L2 d) : Eucl d → ℂ) ξ) = 0 := by
  set f : 𝓢(Eucl d, ℂ) := 𝓕⁻ g with hfdef
  have hFf : 𝓕 f = g := fourier_fourierInv_eq g
  have h1 : inner ℂ (𝓕 (freeLaplacian f + z • toL2 f)) (𝓕 u) = 0 := by
    rw [Lp.inner_fourier_eq]; exact horth f
  have h2 : 𝓕 (freeLaplacian f + z • toL2 f) = toL2 (𝓕 (-(Δ f)) + z • g) := by
    rw [toL2_add, toL2_smul, FourierAdd.fourier_add, FourierSMul.fourier_smul]
    congr 1
    · rw [freeLaplacian, toL2, toL2, SchwartzMap.toLp_fourier_eq]
    · rw [toL2, toL2, SchwartzMap.toLp_fourier_eq, hFf]
  rw [h2, L2.inner_def] at h1
  rw [← h1]
  simp only [toL2]
  apply integral_congr_ae
  filter_upwards [(𝓕 (-(Δ f)) + z • g).coeFn_toLp 2 (volume : Measure (Eucl d))] with ξ hξ
  rw [hξ]
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, RCLike.inner_apply,
    fourier_freeLaplacian_apply, hFf, map_add, map_mul, Complex.conj_ofReal, smul_eq_mul]
  ring

/-- The deficiency criterion: for non-real `z`, the range of `-Δ + z` on the Schwartz core is
dense in `L²(ℝ^d)`. -/
theorem dense_range_freeLaplacian_add_smul {d : ℕ} (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range (fun f : 𝓢(Eucl d, ℂ) => freeLaplacian f + z • toL2 f)) := by
  rw [range_shiftMap, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  have horth : ∀ f : 𝓢(Eucl d, ℂ), inner ℂ (freeLaplacian f + z • toL2 f) u = 0 := by
    intro f
    exact hu _ ⟨f, rfl⟩
  have key := integral_conj_mul_symbol_eq_zero z u horth
  -- On the Fourier side, `u` is annihilated by multiplication by a nowhere vanishing symbol.
  set v : Eucl d → ℂ := ((𝓕 u : L2 d) : Eucl d → ℂ) with hvdef
  set c : Eucl d → ℂ := fun ξ => (symbol ξ : ℂ) + (starRingEnd ℂ) z with hc
  have hccont : Continuous c := by simp only [hc, symbol]; fun_prop
  have hcne : ∀ ξ, c ξ ≠ 0 := by
    intro ξ h
    apply hz
    have him : (c ξ).im = -z.im := by simp [hc]
    rw [h] at him
    simpa using him
  have hvloc : LocallyIntegrable v volume := (Lp.memLp (𝓕 u)).locallyIntegrable one_le_two
  have hwloc : LocallyIntegrable (fun ξ => c ξ * v ξ) volume := by
    rw [← locallyIntegrableOn_univ] at hvloc ⊢
    exact hvloc.continuousOn_mul hccont.continuousOn isClosed_univ.isLocallyClosed
  have hw : ∀ᵐ ξ, c ξ * v ξ = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hwloc
    intro φ hsm hcs
    have hcs' : HasCompactSupport (fun x : Eucl d => ((φ x : ℝ) : ℂ)) :=
      HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hcs (by simp)
    have hsm' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Eucl d => ((φ x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hsm
    have hkey := key (hcs'.toSchwartzMap hsm')
    simp only [HasCompactSupport.toSchwartzMap_toFun, Complex.conj_ofReal] at hkey
    rw [← hkey]
    apply integral_congr_ae
    filter_upwards with ξ
    simp [Complex.real_smul, hc]
  have hvzero : ∀ᵐ ξ, v ξ = 0 := by
    filter_upwards [hw] with ξ hξ
    rcases mul_eq_zero.mp hξ with h | h
    · exact absurd h (hcne ξ)
    · exact h
  have hFu : (𝓕 u : L2 d) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hvzero] with ξ hξ
    simpa [hvdef] using hξ
  have hnorm : ‖u‖ = 0 := by rw [← Lp.norm_fourier_eq u, hFu, norm_zero]
  simpa using norm_eq_zero.mp hnorm

/-- **The free Laplacian is essentially self-adjoint on the Schwartz core**, proved via
Plancherel's theorem.

The three conjuncts are exactly the basic criterion for essential self-adjointness of the
symmetric operator `-Δ` with domain the Schwartz space `𝓢(ℝ^d)` inside `L²(ℝ^d)`:

* the domain is dense in `L²(ℝ^d)`;
* the operator is symmetric on that domain;
* for every non-real `z` (in particular `z = ±i`) the range of `-Δ + z` is dense, i.e. both
  deficiency subspaces of the closure of `-Δ` are trivial.
-/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel (d : ℕ) :
    Dense (Set.range (fun f : 𝓢(Eucl d, ℂ) => toL2 f)) ∧
    (∀ f g : 𝓢(Eucl d, ℂ),
      inner ℂ (freeLaplacian f) (toL2 g) = inner ℂ (toL2 f) (freeLaplacian g)) ∧
    (∀ z : ℂ, z.im ≠ 0 →
      Dense (Set.range (fun f : 𝓢(Eucl d, ℂ) => freeLaplacian f + z • toL2 f))) :=
  ⟨dense_core d, fun f g => freeLaplacian_symmetric f g,
    fun z hz => dense_range_freeLaplacian_add_smul z hz⟩

end Brockian.FreeLaplacianPlancherel

