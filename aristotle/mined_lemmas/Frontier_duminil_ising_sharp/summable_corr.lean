import Mathlib
/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-!
## The Ising model on a finite chain

We set up the nearest-neighbour Ising model with free boundary conditions on the
segment `{0, 1, …, n}` and compute its two-point function exactly.  This is the
one-dimensional base case of the sharpness of the phase transition
(Duminil-Copin–Tassion): the two-point function decays exponentially at *every*
finite inverse temperature, so the critical inverse temperature is `+∞` and the
subcritical phase (exponential decay of correlations, finite susceptibility)
occupies the whole of `[0, ∞)`.
-/

namespace IsingChain

/-- The spin value attached to a Boolean: `true ↦ +1`, `false ↦ -1`. -/

theorem summable_corr (β : ℝ) : Summable (fun n : ℕ => corr β n) := by
  have h : Summable (fun n : ℕ => Real.tanh β ^ n) := by
    apply Summable.of_abs
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg _) (abs_tanh_lt_one β)
  simpa [corr_eq] using h

end IsingChain

/-- **Sharpness of the phase transition for the Ising model (one-dimensional case).**

For the nearest-neighbour Ising model on the chain `{0, …, n}` with free boundary
conditions and inverse temperature `β`:

1. the two-point function is exactly `⟨σ₀ σₙ⟩ = (tanh β)ⁿ`;
2. for every `β` there is `c > 0` with `|⟨σ₀ σₙ⟩| ≤ e^{-c n}` (exponential decay);
3. correlations tend to `0`, so there is no long-range order;
4. the susceptibility `∑ₙ ⟨σ₀ σₙ⟩` converges.

Hence the whole of `[0, ∞)` is subcritical: the critical inverse temperature is
`+∞`, and the subcritical behaviour predicted by the sharpness theorem
(exponential decay of correlations together with finite susceptibility) holds
at every finite inverse temperature. -/
