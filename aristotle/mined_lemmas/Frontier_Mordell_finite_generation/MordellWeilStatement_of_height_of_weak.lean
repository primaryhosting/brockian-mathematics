/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-! ## The multiplication-by-`m` subgroup and its quotient -/

/-- Multiplication by `m` as an endomorphism of an additive commutative group. -/

theorem MordellWeilStatement_of_height_of_weak
    (H : ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ∃ h : E.toAffine.Point → ℝ,
        (∀ Q : E.toAffine.Point, ∃ C : ℝ, ∀ P : E.toAffine.Point, h (P + Q) ≤ 2 * h P + C) ∧
        (∃ C : ℝ, ∀ P : E.toAffine.Point, 4 * h P ≤ h (2 • P) + C) ∧
        (∀ C : ℝ, {P : E.toAffine.Point | h P ≤ C}.Finite) ∧
        Finite (E.toAffine.Point ⧸ smulSubgroup 2 E.toAffine.Point)) :
    MordellWeilStatement := by
  intro E hE
  obtain ⟨h, H1, H2, H3, hfin⟩ := H E hE
  exact @Mordell_finite_generation E hE h H1 H2 H3 hfin

/-- Base case: if the group of rational points is finite, it is finitely generated. -/
