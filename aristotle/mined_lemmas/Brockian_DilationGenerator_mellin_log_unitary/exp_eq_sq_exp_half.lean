/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The substitution `x = e^t` induces a unitary `U : L²(0,∞) ≃ L²(ℝ)`,
`(U f)(t) = e^{t/2} · f(e^t)`, with inverse `(U⁻¹ h)(x) = x^{-1/2} · h(log x)`.

We formalise this at the level of integrals and `L²`-seminorms:

* `Brockian.DilationGenerator.mellin_log_unitary` — the Bochner integral identity
  `∫ x in Ioi 0, ‖f x‖² = ∫ t, ‖e^{t/2} • f (e^t)‖²`, with no hypotheses on `f`;
* `Brockian.DilationGenerator.lintegral_norm_sq_comp_exp` — the same identity for the
  lower Lebesgue integral (so it also carries the information that one side is infinite
  exactly when the other is);
* `Brockian.DilationGenerator.eLpNorm_comp_exp` — consequently `U` preserves the
  `L²`-seminorm, `eLpNorm f 2 (volume.restrict (Ioi 0)) = eLpNorm (U f) 2 volume`;
* `Brockian.DilationGenerator.mellin_log_unitary_symm` — the corresponding identity for
  the inverse substitution `x ↦ x^{-1/2} • h (log x)`;
* `Brockian.DilationGenerator.measurePreserving_exp_withDensity` — the underlying pushforward
  statement: `Real.exp` maps the weighted measure `e^t dt` on `ℝ` to Lebesgue measure on `(0,∞)`;
* `Brockian.DilationGenerator.mellin_log_inv_apply` and
  `Brockian.DilationGenerator.mellin_log_apply_inv` — the two pointwise inversion
  identities, showing the displayed formulas are mutually inverse.

The key input is the one-dimensional change-of-variables formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (and its `lintegral` counterpart
`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`) applied to `Real.exp`, whose image
of `univ` is `Ioi 0` and whose derivative is `exp`.

BLOCKED: packaging these statements into a `LinearIsometryEquiv (Lp E 2 (volume.restrict (Ioi 0)))
(Lp E 2 volume)` is not carried out here; it additionally requires the quotient-level
well-definedness of `f ↦ (fun t => e^{t/2} • f (e^t))` on a.e.-equivalence classes and a surjectivity
argument, which are left for future work.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory Set

namespace Brockian
namespace DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


private theorem exp_eq_sq_exp_half (t : ℝ) : Real.exp t = Real.exp (t / 2) ^ 2 := by
  rw [sq, ← Real.exp_add]; ring_nf

/-- The change of variables `x = exp t` identifies the `L²`-norm on `(0, ∞)` with the `L²`-norm
on `ℝ` after the substitution `f ↦ (fun t => exp (t / 2) • f (exp t))`.

This is the analytic heart of the statement that the logarithmic (Mellin) substitution
`U : L²(0,∞) ≃ L²(ℝ)`, `(U f)(t) = e^{t/2} f(e^t)`, is unitary: it says that `U` preserves the
squared `L²` integral. No hypotheses on `f` are needed, since the change-of-variables formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` holds for an arbitrary integrand. -/
