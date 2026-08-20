/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Finset MeasureTheory Metric Module Real Set

/-! ## The Pfaffian of the curvature form of the unit round sphere -/

section Pfaffian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First index of the `i`-th pair `(2i, 2i+1)`. -/

theorem spherePfaffian_eq (m : ℕ) (v : Fin (2 * m) → V) :
    spherePfaffian m v = ((2 * m)! / (2 ^ m * (m)!) : ℝ) • ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
  have hterm : ∀ σ : Equiv.Perm (Fin (2 * m)),
      (Equiv.Perm.sign σ : ℝ) • pairProd m (v ∘ σ) = ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
    intro σ
    rw [pairProd_perm, smul_smul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [spherePfaffian, Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp

end Pfaffian

/-! ## The total surface measure of the round sphere `S^{2m}` -/

/-- The `2m`-dimensional surface measure of the unit sphere `S^{2m} ⊆ ℝ^{2m+1}`, obtained from
the Lebesgue measure by the polar coordinate decomposition. -/
