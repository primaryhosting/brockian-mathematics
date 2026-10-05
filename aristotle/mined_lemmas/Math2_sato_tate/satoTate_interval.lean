/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

theorem satoTate_interval {θ : ℕ → ℝ} (hST : SatoTateEquidistributed θ)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    Tendsto
      (fun X : ℕ => ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ))
        / (primesBelow X).card)
      atTop (𝓝 (∫ x in α..β, satoTateDensity x)) := by
  have hpi := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set L := ∫ x in α..β, satoTateDensity x with hL
  set ε : ℝ := δ * Real.pi / 32 with hεdef
  have hε : 0 < ε := by positivity
  have hεsmall : 4 / Real.pi * ε = δ / 8 := by
    rw [hεdef]; field_simp; ring
  -- the two continuous test functions
  have hg := hST (trap (α - ε) (β + ε) ε) (continuous_trap _ _ _)
  have hf := hST (trap α β ε) (continuous_trap _ _ _)
  rw [Metric.tendsto_atTop] at hg hf
  obtain ⟨N₁, hN₁⟩ := hg (δ / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hf (δ / 4) (by linarith)
  refine ⟨max (max N₁ N₂) 3, fun X hX => ?_⟩
  have hX₁ : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX₂ : N₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX₃ : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hP : (0 : ℝ) < (primesBelow X).card := by
    exact_mod_cast primesBelow_card_pos hX₃
  have hgX := hN₁ X hX₁
  have hfX := hN₂ X hX₂
  rw [Real.dist_eq, abs_lt] at hgX hfX
  -- counting sandwich
  have hup : ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ)) / (primesBelow X).card
      ≤ (∑ p ∈ primesBelow X, trap (α - ε) (β + ε) ε (θ p)) / (primesBelow X).card := by
    gcongr
    exact card_le_sum_trap_upper θ X hε
  have hlow : (∑ p ∈ primesBelow X, trap α β ε (θ p)) / (primesBelow X).card
      ≤ ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ)) / (primesBelow X).card := by
    gcongr
    exact sum_trap_lower_le_card θ X hε
  have hIup := integral_trap_upper hε hαβ
  have hIlow := integral_trap_lower hε hα hαβ hβ
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Sato–Tate.**  Let `E` be an elliptic curve over `ℚ` without complex multiplication and,
for each prime `p` of good reduction, let `a p` be the trace of Frobenius, so that the
Frobenius angle is `θ_p = arccos (a_p / (2 √p)) ∈ [0, π]`.  The Sato–Tate theorem
(Clozel–Harris–Shepherd-Barron–Taylor) asserts that these angles are equidistributed with
respect to the measure `(2/π) sin²θ dθ`; this is the hypothesis `hST`.

The conclusion is the distributional form of the statement: for every subinterval
`[α, β] ⊆ [0, π]`, the density of primes whose Frobenius angle lies in `[α, β]` equals
`(2/π) ∫_α^β sin²x dx`.

The hypothesis is no stronger than the conclusion: by `Math2.satoTate_iff_intervals` the
test-function form `SatoTateEquidistributed` and the interval form `SatoTateIntervals`
are equivalent for angles in `[0, π]`. -/
