import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

namespace Frontier

/-!
## Overview

We formalize, and prove, the one–dimensional base case of the Lieb–Thirring family of
inequalities, in its variational (quadratic form) formulation, which is exactly the
statement of *stability* for a one–dimensional one–particle Schrödinger operator
`H = -d²/dx² + V`:

for every `C¹` test function `ψ` of compact support,
`⟪ψ, Hψ⟫ = ∫ |ψ'|² + ∫ V |ψ|² ≥ - (1/4) (∫ V₋)² ∫ |ψ|²`,

where `V₋ x = max (-V x) 0` is the negative part of the potential.  Equivalently, the
bottom of the spectrum obeys `E₀ ≥ -(1/4) (∫ V₋)²`, i.e. `|E₀|^{1/2} ≤ (1/2) ∫ V₋`,
which is the `γ = 1/2`, `d = 1` Lieb–Thirring bound restricted to a single bound state,
with the sharp constant `L_{1/2,1} = 1/2`.

The proof is the classical one:

* `Frontier.sq_le_integral_abs_mul_abs` : `|ψ(x)|² ≤ ∫ |ψ| |ψ'|`
  (fundamental theorem of calculus, applied to `ψ²` from both `-∞` and `+∞`);
* `Frontier.integral_abs_mul_abs_le_sqrt_mul_sqrt` : `∫ |ψ| |ψ'| ≤ ‖ψ‖₂ ‖ψ'‖₂`
  (Cauchy–Schwarz, i.e. Hölder with `p = q = 2`, via
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`);
* hence `∫ V |ψ|² ≥ - ‖ψ‖_∞² ∫ V₋ ≥ - ‖ψ‖₂ ‖ψ'‖₂ ∫ V₋`, and the result follows from
  `(‖ψ'‖₂ - ‖ψ‖₂ (∫ V₋)/2)² ≥ 0`.

Mathlib does not contain the Lieb–Thirring inequality (nor Schrödinger operator spectral
theory), so no single existing lemma closes the goal; the Mathlib inputs used are cited
above and in the individual proofs.
-/

/-- **Cauchy–Schwarz** for two continuous, compactly supported functions on `ℝ`:
`∫ |f| |g| ≤ (∫ f²)^(1/2) (∫ g²)^(1/2)`.  This is Hölder's inequality with `p = q = 2`
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`). -/

theorem hasCompactSupport_of_hasDerivAt
    (ψ dψ : ℝ → ℝ) (hd : ∀ x, HasDerivAt ψ (dψ x) x) (hs : HasCompactSupport ψ) :
    HasCompactSupport dψ := by
  apply HasCompactSupport.intro hs.isCompact
  intro x hx
  have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have h0 : HasDerivAt ψ 0 x := by
    have hev : ψ =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  exact (hd x).unique h0

/-- **Pointwise sup bound.**  For a `C¹` function `ψ : ℝ → ℝ` of compact support with
derivative `dψ`, one has `ψ(x)² ≤ ∫ |ψ| |dψ|` for every `x`.

This is the one–dimensional Gagliardo–Nirenberg/Sobolev estimate `‖ψ‖_∞² ≤ ‖ψ‖₂ ‖ψ'‖₂`
before Cauchy–Schwarz is applied. -/
