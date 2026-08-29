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

theorem satoTate_proportion_tendsto {θ : ℕ → ℝ} (h : SatoTateDistributed θ)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    Tendsto (fun N => angleProportion θ α β N) atTop (𝓝 (∫ t in α..β, stDensity t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set I : ℝ := ∫ t in α..β, stDensity t with hI
  set δ : ℝ := min 1 (ε * π / 32) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδsmall : (2 / π) * (2 * δ) ≤ ε / 8 := by
    have h1 : δ ≤ ε * π / 32 := min_le_right _ _
    have hπ : (0:ℝ) < π := Real.pi_pos
    rw [div_mul_eq_mul_div, mul_comm]
    rw [div_le_iff₀ hπ]
    nlinarith
  have hup := h (bumpUpper α β δ) (continuous_bumpUpper α β δ)
  have hlo := h (bumpLower α β δ) (continuous_bumpLower α β δ)
  rw [Metric.tendsto_atTop] at hup hlo
  obtain ⟨N₁, hN₁⟩ := hup (ε / 8) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hlo (ε / 8) (by linarith)
  refine ⟨max (max N₁ N₂) 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h1 : |primeAvg θ (bumpUpper α β δ) N - stIntegral (bumpUpper α β δ)| < ε / 8 := by
    have := hN₁ N hNa; rwa [Real.dist_eq] at this
  have h2 : |primeAvg θ (bumpLower α β δ) N - stIntegral (bumpLower α β δ)| < ε / 8 := by
    have := hN₂ N hNb; rwa [Real.dist_eq] at this
  have hupI := stIntegral_bumpUpper_le hδ hα hαβ hβ
  have hloI := stIntegral_bumpLower_ge hδ hα hαβ hβ
  have hmono1 : primeAvg θ (indIcc α β) N ≤ primeAvg θ (bumpUpper α β δ) N :=
    primeAvg_mono hN2 (ind_le_bumpUpper hδ)
  have hmono2 : primeAvg θ (bumpLower α β δ) N ≤ primeAvg θ (indIcc α β) N :=
    primeAvg_mono hN2 (bumpLower_le_ind hδ)
  rw [Real.dist_eq, angleProportion_eq_primeAvg]
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> [linarith; linarith]


/-- **Sato–Tate for Frobenius angles, counting form.**  If the symmetric power Weyl sums of a
trace-of-Frobenius function tend to `0`, then for every `[α, β] ⊆ [0, π]` the proportion of
primes `p ≤ N` whose Frobenius angle lies in `[α, β]` tends to the Sato–Tate measure
`∫_α^β (2/π) sin²t dt` of the interval. -/
