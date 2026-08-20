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

open MeasureTheory Complex

/-- Auxiliary product `x ↦ x · f x · conj (g x)` whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/

lemma contDiff_prodAux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ (1 : WithTop ℕ∞) (prodAux f g) := by
  have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => (y : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prodAux f g) :=
    (hx.mul hf).mul (contDiff_conj hg)
  exact this.of_le (by exact_mod_cast le_top)

