/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The **Gagliardo–Nirenberg(–Sobolev) interpolation inequality**.

Let `E` be a finite-dimensional real normed space of dimension `n > 0`, equipped with an additive
Haar measure `μ`, and let `F` be a finite-dimensional real normed space.  Let `1 ≤ p` and let `p'`
be the Sobolev conjugate exponent, i.e. `(p')⁻¹ = p⁻¹ - n⁻¹`.  Then there is a constant `C`,
depending only on `E`, `F`, `μ` and `p` (in particular independent of the function), such that for
every continuously differentiable compactly supported `u : E → F` the `L^{p'}` norm of `u` is
bounded by `C` times the `L^p` norm of its Fréchet derivative.

This is obtained from Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, whose explicit
constant is `MeasureTheory.SNormLESNormFDerivOfEqConst F μ p`. -/

theorem nirenberg_gagliardo_euclidean {n : ℕ} (hn : 2 ≤ n) {p' : ℝ≥0}
    (hp' : (p' : ℝ) = n / (n - 1)) :
    ∃ C : ℝ≥0, ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      MeasureTheory.eLpNorm u p' MeasureTheory.volume ≤
        C * MeasureTheory.eLpNorm (fderiv ℝ u) 1 MeasureTheory.volume := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have key := nirenberg_gagliardo (E := EuclideanSpace ℝ (Fin n)) (F := ℝ)
    MeasureTheory.volume (p := 1) (p' := p') le_rfl (by rw [hrank]; omega) ?_
  · simpa using key
  · rw [hp', hrank]
    have h0 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hnpos : (n : ℝ) ≠ 0 := by linarith
    field_simp
    push_cast
    ring

end Frontier

