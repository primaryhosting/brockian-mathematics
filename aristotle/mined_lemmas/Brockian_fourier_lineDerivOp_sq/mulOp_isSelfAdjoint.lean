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
# The Fourier transform of the Laplacian on Schwartz space

We record the classical formula `𝓕 (Δ f) ξ = -(4π²‖ξ‖²) 𝓕 f ξ` for Schwartz functions,
introduce the Fourier symbol `freeSymbol ξ = 4π²‖ξ‖²` of the free Laplacian `-Δ`, and show that
the "resolvent multiplier" `ξ ↦ (1 + freeSymbol ξ)⁻¹` has temperate growth (so that multiplying
a Schwartz function by it produces again a Schwartz function).
-/

namespace Brockian

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem mulOp_isSelfAdjoint (hd : Dense ((mulOp m).domain : Set (L2 V))) :
    IsSelfAdjoint (mulOp m) := by
  have hdom : ((mulOp m).adjoint).domain ≤ (mulOp m).domain := by
    intro y hy
    set w : L2 V := (mulOp m).adjoint ⟨y, hy⟩ with hw
    have hadj : ∀ x : (mulOp m).domain, inner ℂ w (x : L2 V) = inner ℂ y ((mulOp m) x) :=
      fun x => LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ x
    set v : V → ℂ := ((y : L2 V) : V → ℂ) with hv
    have hvLp : MemLp v 2 (volume : Measure V) := Lp.memLp y
    have hvmeas : AEStronglyMeasurable v (volume : Measure V) := hvLp.1
    have hmc : AEStronglyMeasurable (fun x => (m x : ℂ)) (volume : Measure V) :=
      (Complex.continuous_ofReal.comp hm).aestronglyMeasurable
    set S : ℕ → Set V := fun n => {x | |m x| ≤ (n : ℝ)} with hS
    have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
      measurableSet_le (hm.abs.measurable) measurable_const
    set g : ℕ → V → ℂ := fun n => (S n).indicator (fun x => (m x : ℂ) * v x) with hg
    have hgmeas : ∀ n, AEStronglyMeasurable (g n) (volume : Measure V) := fun n =>
      (hmc.mul hvmeas).indicator (hSmeas n)
    have hgbound : ∀ n x, ‖g n x‖ ≤ ‖(((n : ℝ) : ℂ)) * v x‖ := by
      intro n x
      have hrhs : ‖(((n : ℝ) : ℂ)) * v x‖ = (n : ℝ) * ‖v x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
      rw [hrhs]
      by_cases hx : x ∈ S n
      · have hga : g n x = (m x : ℂ) * v x := by simp [hg, Set.indicator_of_mem hx]
        have hmn : |m x| ≤ (n : ℝ) := hx
        rw [hga, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hmn (norm_nonneg _)
      · have hga : g n x = 0 := by simp [hg, Set.indicator_of_notMem hx]
        rw [hga, norm_zero]
        positivity
    have hgLp : ∀ n, MemLp (g n) 2 (volume : Measure V) := fun n =>
      MemLp.of_le (hvLp.const_mul ((n : ℝ) : ℂ)) (hgmeas n)
        (Filter.Eventually.of_forall (hgbound n))
    set xn : ℕ → L2 V := fun n => (hgLp n).toLp (g n) with hxn
    have hxncoe : ∀ n, ((xn n : L2 V) : V → ℂ) =ᵐ[volume] g n := fun n => MemLp.coeFn_toLp _
    have hxnmem : ∀ n, xn n ∈ (mulOp m).domain := by
      intro n
      have hbound : ∀ x, ‖(m x : ℂ) * g n x‖ ≤ ‖(((n : ℝ) ^ 2 : ℝ) : ℂ) * v x‖ := by
        intro x
        have hrhs : ‖(((n : ℝ) ^ 2 : ℝ) : ℂ) * v x‖ = ((n : ℝ) ^ 2) * ‖v x‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ 2)]
        rw [hrhs]
        by_cases hx : x ∈ S n
        · have hga : g n x = (m x : ℂ) * v x := by simp [hg, Set.indicator_of_mem hx]
          have hmn : |m x| ≤ (n : ℝ) := hx
          have h3 : |m x * m x| ≤ (n : ℝ) ^ 2 := by
            rw [abs_mul]
            nlinarith [abs_nonneg (m x)]
          rw [hga, ← mul_assoc, ← Complex.ofReal_mul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        · have hga : g n x = 0 := by simp [hg, Set.indicator_of_notMem hx]
          rw [hga, mul_zero, norm_zero]
          positivity
      have hmem : MemLp (fun x => (m x : ℂ) * g n x) 2 (volume : Measure V) :=
        MemLp.of_le (hvLp.const_mul (((n : ℝ) ^ 2 : ℝ) : ℂ)) (hmc.mul (hgmeas n))
          (Filter.Eventually.of_forall hbound)
      show MemLp (fun x => (m x : ℂ) * ((xn n : L2 V) : V → ℂ) x) 2 (volume : Measure V)
      refine hmem.ae_eq ?_
      filter_upwards [hxncoe n] with x hx
      rw [hx]
    have hnorm : ∀ n, ‖xn n‖ ≤ ‖w‖ := by
      intro n
      have hinner : inner ℂ (y : L2 V) ((mulOp m) ⟨xn n, hxnmem n⟩)
          = inner ℂ (xn n : L2 V) (xn n : L2 V) := by
        rw [L2.inner_def, L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_mulOp m ⟨xn n, hxnmem n⟩, hxncoe n] with a h1 h2
        rw [h1, h2]
        by_cases hx : a ∈ S n
        · have hga : g n a = (m a : ℂ) * v a := by simp [hg, Set.indicator_of_mem hx]
          rw [hga]
          simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
          ring
        · have hga : g n a = 0 := by simp [hg, Set.indicator_of_notMem hx]
          rw [hga]
          simp [RCLike.inner_apply]
      have h1 : ((‖xn n‖ : ℂ)) ^ 2 = inner ℂ w (xn n : L2 V) := by
        rw [hadj ⟨xn n, hxnmem n⟩, hinner, inner_self_eq_norm_sq_to_K]
        norm_cast
      have h2 : ‖xn n‖ ^ 2 ≤ ‖w‖ * ‖xn n‖ := by
        have := congrArg Norm.norm h1
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
        rw [this]
        exact norm_inner_le_norm (𝕜 := ℂ) w (xn n : L2 V)
      rcases eq_or_lt_of_le (norm_nonneg (xn n)) with h0 | h0
      · rw [← h0]; exact norm_nonneg _
      · exact le_of_mul_le_mul_right (by nlinarith) h0
    -- pass to the limit
    have hlim : ∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (nhds ((m x : ℂ) * v x)) := by
      intro x
      obtain ⟨N, hN⟩ := exists_nat_ge |m x|
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hx : x ∈ S n := le_trans hN (by exact_mod_cast hn)
      simp [hg, Set.indicator_of_mem hx]
    have heLp : ∀ n, eLpNorm (g n) 2 (volume : Measure V) ≤ ENNReal.ofReal ‖w‖ := by
      intro n
      have hfin : eLpNorm (g n) 2 (volume : Measure V) ≠ ⊤ := (hgLp n).2.ne
      have hn : (eLpNorm (g n) 2 (volume : Measure V)).toReal ≤ ‖w‖ := by
        have := hnorm n
        rwa [Lp.norm_def, eLpNorm_congr_ae (hxncoe n)] at this
      calc eLpNorm (g n) 2 (volume : Measure V)
          = ENNReal.ofReal (eLpNorm (g n) 2 (volume : Measure V)).toReal := by
            rw [ENNReal.ofReal_toReal hfin]
        _ ≤ ENNReal.ofReal ‖w‖ := ENNReal.ofReal_le_ofReal hn
    have hfinal : eLpNorm (fun x => (m x : ℂ) * v x) 2 (volume : Measure V)
        ≤ ENNReal.ofReal ‖w‖ :=
      MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall heLp) hgmeas
        (Filter.Eventually.of_forall hlim)
    exact ⟨hmc.mul hvmeas, lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top⟩
  have hle : (mulOp m).adjoint ≤ mulOp m := by
    refine ⟨hdom, ?_⟩
    intro p q hpq
    refine hd.eq_of_inner_left ?_
    intro z
    have h1 : inner ℂ ((mulOp m).adjoint p) (z : L2 V) = inner ℂ (p : L2 V) ((mulOp m) z) :=
      LinearPMap.adjoint_isFormalAdjoint hd p z
    have h2 : inner ℂ ((mulOp m) q) (z : L2 V) = inner ℂ (q : L2 V) ((mulOp m) z) :=
      mulOp_isFormalAdjoint m q z
    rw [h1, h2, hpq]
  exact le_antisymm hle (LinearPMap.IsFormalAdjoint.le_adjoint hd (mulOp_isFormalAdjoint m))

end mul

end

end Brockian

import Brockian.MultiplicationOperator
import Brockian.SchwartzFourierLaplacian

/-!
# The Laplacian on the Schwartz core

We embed the Schwartz space into `L²(V; ℂ)` and define `negLaplacianCore`, the operator `-Δ`
with domain the (dense) subspace of Schwartz functions.
-/

namespace Brockian

open MeasureTheory SchwartzMap Filter LinearPMap LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The embedding of the Schwartz space into `L²`. -/
