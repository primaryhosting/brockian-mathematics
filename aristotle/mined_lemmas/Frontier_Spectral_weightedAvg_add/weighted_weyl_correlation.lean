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
# Weighted Weyl bridge for Liouville correlation

This module proves an **analytic transfer theorem**: for a bounded complex weight `w`
and an arbitrary real sequence `x`, vanishing of the weighted Weyl sums against *every*
Fourier mode `fourier k` (including the trivial mode `k = 0`) forces vanishing of the
weighted averages against *every* continuous observable on the circle `𝕋 = AddCircle 1`.

The point of the module is to isolate the genuinely open arithmetic input.  Nothing here
proves any cancellation for the Liouville function: the Fourier cancellation is carried as
an *explicit hypothesis* in every statement below.

## Status labels

* `Frontier.Spectral.weighted_weyl_correlation` — **STANDARD**: a kernel-verified,
  unconditional theorem of functional analysis (density of the Fourier span in
  `C(𝕋, ℂ)` plus a uniform `‖·‖ ≤ 1` bound, via a `3ε` argument).
* `Frontier.Spectral.liouville_continuous_correlation_of_fourier` — **CONDITIONAL**:
  the Fourier-cancellation input `hfourier` is an explicit, unproved hypothesis.  This is
  *not* a proof of Chowla's conjecture, of Sarnak's conjecture, or of any unconditional
  decorrelation statement for `λ(n)`.
-/
import Mathlib

open Filter Topology Finset Submodule Set

noncomputable section

namespace Frontier.Spectral

/-- The circle `𝕋 = ℝ / ℤ`, realised as `AddCircle (1 : ℝ)`. -/
abbrev Torus : Type := AddCircle (1 : ℝ)

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The weighted Weyl average
`weightedAvg w x F N = N⁻¹ * ∑_{n < N} w n * F (x n mod 1)`. -/

theorem weighted_weyl_correlation {w : ℕ → ℂ} {x : ℕ → ℝ}
    (hw : ∀ n, ‖w n‖ ≤ 1)
    (hfourier : ∀ k : ℤ, Tendsto (weightedAvg w x (fourier k)) atTop (𝓝 0))
    (F : C(Torus, ℂ)) :
    Tendsto (weightedAvg w x F) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- density of the Fourier span
  have hmem : F ∈ (span ℂ (Set.range (fun k : ℤ => fourier (T := 1) k))).topologicalClosure := by
    rw [span_fourier_closure_eq_top (T := 1)]
    trivial
  have hclosure : F ∈ closure ((span ℂ (Set.range (fun k : ℤ => fourier (T := 1) k))) : Set _) :=
    hmem
  obtain ⟨G, hGmem, hGdist⟩ := Metric.mem_closure_iff.mp hclosure (ε / 3) (by linarith)
  have hGtend := tendsto_weightedAvg_of_mem_span hfourier hGmem
  rw [Metric.tendsto_atTop] at hGtend
  obtain ⟨M, hM⟩ := hGtend (ε / 3) (by linarith)
  refine ⟨M, fun n hn => ?_⟩
  have hMn := hM n hn
  rw [dist_eq_norm, sub_zero] at hMn ⊢
  have hsplit : weightedAvg w x F n
      = weightedAvg w x (F - G) n + weightedAvg w x G n := by
    rw [weightedAvg_sub]; ring
  have hbound : ‖weightedAvg w x (F - G) n‖ ≤ ‖F - G‖ := norm_weightedAvg_le hw _ _
  have hFG : ‖F - G‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hGdist
  calc ‖weightedAvg w x F n‖
      ≤ ‖weightedAvg w x (F - G) n‖ + ‖weightedAvg w x G n‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ < ε / 3 + ε / 3 := by
        exact add_lt_add (hbound.trans_lt hFG) hMn
    _ < ε := by linarith

end Generic

/-! ### The Liouville specialization

Mathlib (at the pinned version) has no canonical Liouville arithmetic function, so we
define it from prime-factor multiplicity in the standard way, using Mathlib's
`ArithmeticFunction.cardFactors` (the function `Ω`, counting prime factors with
multiplicity):
`λ(n) = (-1)^{Ω(n)}`.  This is the classical Liouville function; the lemmas below record
that it is unimodular, completely multiplicative, and takes the value `-1` at primes, so
it cannot be mistaken for an arbitrary unconstrained weight. -/

/-- The Liouville function `λ(n) = (-1)^{Ω(n)}`, valued in `ℂ`, where `Ω = cardFactors`
counts prime factors with multiplicity. -/
