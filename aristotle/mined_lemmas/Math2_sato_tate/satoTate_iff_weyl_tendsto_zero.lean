import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

set_option grind.warning false

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

theorem satoTate_iff_weyl_tendsto_zero (θ : ℕ → ℝ) (hθ : ∀ p, θ p ∈ Icc (0:ℝ) π) :
    SatoTateDistributed θ ↔
      ∀ m : ℕ, 1 ≤ m → Tendsto (fun N => primeAvg θ (weyl m) N) atTop (𝓝 0) := by
  constructor
  · intro h m hm
    have h' := h (weyl m) (continuous_weyl m)
    rwa [stIntegral_weyl_eq_zero hm] at h'
  · intro hW
    have key : ∀ m : ℕ,
        Tendsto (fun N => primeAvg θ (weyl m) N) atTop (𝓝 (stIntegral (weyl m))) := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [weyl_zero, stIntegral_one]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop 2] with N hN
        exact (primeAvg_const θ hN 1).symm
      · rw [stIntegral_weyl_eq_zero hm]
        exact hW m hm
    intro f hf
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n, c, hc⟩ := exists_weyl_approx hf (show (0:ℝ) < ε / 4 by linarith)
    let g : ℝ → ℝ := fun t => ∑ m ∈ Finset.range n, c m * weyl m t
    have hgcont : Continuous g :=
      continuous_finset_sum _ fun m _ => continuous_const.mul (continuous_weyl m)
    have hgint : stIntegral g = ∑ m ∈ Finset.range n, c m * stIntegral (weyl m) := by
      have h := stIntegral_sum (Finset.range n) (fun m t => c m * weyl m t)
        (fun m _ => continuous_const.mul (continuous_weyl m))
      simpa [g, stIntegral_const_mul] using h
    have hgavg : Tendsto (fun N => primeAvg θ g N) atTop (𝓝 (stIntegral g)) := by
      rw [hgint]
      have hrw : ∀ N, primeAvg θ g N = ∑ m ∈ Finset.range n, c m * primeAvg θ (weyl m) N := by
        intro N
        have h := primeAvg_sum θ (Finset.range n) (fun m t => c m * weyl m t) N
        simpa [g, primeAvg_const_mul] using h
      simp only [hrw]
      exact tendsto_finset_sum _ fun m _ => (key m).const_mul (c m)
    rw [Metric.tendsto_atTop] at hgavg
    obtain ⟨N₀, hN₀⟩ := hgavg (ε / 2) (by linarith)
    refine ⟨max N₀ 2, fun N hN => ?_⟩
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have h1 : |primeAvg θ f N - primeAvg θ g N| ≤ ε / 4 := by
      rw [← primeAvg_sub]
      exact abs_primeAvg_le hN2 hθ fun t ht => hc t ht
    have h2 : |stIntegral f - stIntegral g| ≤ ε / 4 := by
      rw [← stIntegral_sub hf hgcont]
      exact abs_stIntegral_le (hf.sub hgcont) fun t ht => hc t ht
    have h3 : |primeAvg θ g N - stIntegral g| < ε / 2 := by
      have := hN₀ N hNN₀
      rwa [Real.dist_eq] at this
    have h2' : |stIntegral g - stIntegral f| ≤ ε / 4 := by rwa [abs_sub_comm] at h2
    have t1 := abs_sub_le (primeAvg θ f N) (stIntegral g) (stIntegral f)
    have t2 := abs_sub_le (primeAvg θ f N) (primeAvg θ g N) (stIntegral g)
    rw [Real.dist_eq]
    linarith

/-- Under the Hasse bound, the Frobenius angle really does satisfy `a_p = 2 √p cos θ_p`. -/
