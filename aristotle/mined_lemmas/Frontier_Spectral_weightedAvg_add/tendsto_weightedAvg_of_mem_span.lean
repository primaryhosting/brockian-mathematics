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

theorem tendsto_weightedAvg_of_mem_span
    (hfourier : ∀ k : ℤ, Tendsto (weightedAvg w x (fourier k)) atTop (𝓝 0))
    {F : C(Torus, ℂ)} (hF : F ∈ span ℂ (Set.range (fun k : ℤ => fourier (T := 1) k))) :
    Tendsto (weightedAvg w x F) atTop (𝓝 0) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨k, rfl⟩ := hF
      exact hfourier k
  | zero =>
      have heq : weightedAvg w x 0 = fun _ : ℕ => (0 : ℂ) := funext fun N => weightedAvg_zero_fun N
      rw [heq]
      exact tendsto_const_nhds
  | add F G _ _ hF hG =>
      have heq : weightedAvg w x (F + G) = fun N => weightedAvg w x F N + weightedAvg w x G N :=
        funext fun N => weightedAvg_add F G N
      rw [heq]
      simpa using hF.add hG
  | smul c F _ hF =>
      have heq : weightedAvg w x (c • F) = fun N => c * weightedAvg w x F N :=
        funext fun N => weightedAvg_smul c F N
      rw [heq]
      simpa using hF.const_mul c

/-- **STANDARD (unconditional).**  Weighted Weyl bridge: for a weight bounded by `1`,
vanishing of the weighted Weyl sums along every Fourier mode `fourier k`, `k : ℤ`
(including `k = 0`), implies vanishing of the weighted averages against every continuous
observable `F : C(𝕋, ℂ)`.

The proof combines the uniform bound `norm_weightedAvg_le` with the density of the span
of the Fourier monomials in `C(𝕋, ℂ)` (`span_fourier_closure_eq_top`) in a `3ε`
argument. -/
