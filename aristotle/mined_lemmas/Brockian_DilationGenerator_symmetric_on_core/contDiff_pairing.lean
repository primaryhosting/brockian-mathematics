import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
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

namespace Brockian
namespace DilationGenerator

open MeasureTheory

/-- The auxiliary function `x ↦ x · f(x) · conj(g(x))`, whose derivative is exactly the
integrand appearing in the difference of the two sides of the symmetry identity. -/

theorem contDiff_pairing {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ 1 (pairing f g) := by
  have hcg : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (starRingEnd ℂ) (g x)) :=
    Complex.conjCLE.contDiff.comp hg
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff.of_le le_top
  exact (((hx.mul hf).mul hcg).of_le (by exact_mod_cast le_top))

