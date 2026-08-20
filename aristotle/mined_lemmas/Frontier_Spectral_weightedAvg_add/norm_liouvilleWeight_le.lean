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

lemma norm_liouvilleWeight_le (n : ℕ) : ‖liouvilleWeight n‖ ≤ 1 :=
  (norm_liouvilleWeight n).le

/-- **CONDITIONAL.**  Liouville specialization of the weighted Weyl bridge.

*Hypothesis* `hfourier` is the genuinely open arithmetic input: cancellation of the
Liouville-weighted Weyl sums along every Fourier mode `fourier k` (`k : ℤ`, including
`k = 0`, which is the prime-number-theorem-type input `N⁻¹ ∑_{n<N} λ(n) → 0`).  It is
assumed here, not proved.

*Conclusion*: the Liouville-weighted averages then vanish against every continuous
observable on the circle.

This statement is therefore **not** a proof of Chowla's or Sarnak's conjecture, nor of
any unconditional decorrelation theorem for `λ(n)`. -/
