import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

open Set MeasureTheory Filter Topology

/-!
## The classical fluctuation–dissipation relation

Let `C t = ⟨A(0) A(t)⟩` be the equilibrium autocorrelation function of an observable `A`
in a system at inverse temperature `β`.  The (classical, Kubo) fluctuation–dissipation

theorem fluctuation_dissipation_interval
    (β T : ℝ) (C C' χ : ℝ → ℝ)
    (hC : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt C (C' t) t)
    (hC'int : IntervalIntegrable C' volume 0 T)
    (hχ : ∀ t, χ t = -β * C' t) :
    ∫ t in (0 : ℝ)..T, χ t = β * (C 0 - C T) := by
  have h : ∫ t in (0 : ℝ)..T, χ t = ∫ t in (0 : ℝ)..T, -β * C' t := by
    simp only [hχ]
  rw [h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hC hC'int]
  ring

/-- **Fluctuation–dissipation theorem (static susceptibility sum rule).**

Let `C` be the equilibrium autocorrelation function `C t = ⟨A(0) A(t)⟩` of an observable
of a system at inverse temperature `β`, with derivative `C'` on `(0, ∞)`, and let
`χ` be the linear response (after-effect) function, related to `C` by the classical
fluctuation–dissipation relation `χ t = -β * C' t`.

If the correlations decay to `Cinf` at large times and `C'` is integrable, then the
static susceptibility -- the total integrated response -- equals `β` times the
equilibrium fluctuation `C 0 - Cinf`:

`∫_0^∞ χ(t) dt = β * (C 0 - Cinf)`.

In particular, when the correlations decay to zero (`Cinf = 0`), the dissipative
response `∫_0^∞ χ` is `β = 1 / (k_B T)` times the equal-time fluctuation `⟨A²⟩ = C 0`. -/
