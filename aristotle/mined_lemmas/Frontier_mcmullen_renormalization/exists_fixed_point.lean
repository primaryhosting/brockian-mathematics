/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

lemma exists_fixed_point (c : ℂ) : ∃ z : ℂ, qmap c z = z ∧ ‖z‖ ^ 2 ≤ ‖c‖ := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = 1 - 4 * c := IsAlgClosed.exists_pow_nat_eq (1 - 4 * c) two_pos
  set z₁ : ℂ := (1 + s) / 2 with hz₁
  set z₂ : ℂ := (1 - s) / 2 with hz₂
  have hprod : z₁ * z₂ = c := by
    simp only [hz₁, hz₂]
    field_simp
    linear_combination -hs
  have hfix₁ : qmap c z₁ = z₁ := by
    simp only [qmap, hz₁]
    field_simp
    linear_combination hs
  have hfix₂ : qmap c z₂ = z₂ := by
    simp only [qmap, hz₂]
    field_simp
    linear_combination hs
  have hnorm : ‖z₁‖ * ‖z₂‖ = ‖c‖ := by rw [← norm_mul, hprod]
  rcases le_total ‖z₁‖ ‖z₂‖ with h | h
  · exact ⟨z₁, hfix₁, by nlinarith [norm_nonneg z₁, norm_nonneg z₂]⟩
  · exact ⟨z₂, hfix₂, by nlinarith [norm_nonneg z₁, norm_nonneg z₂]⟩

/-- The filled Julia set of a quadratic map is nonempty: it contains a fixed
point. -/
