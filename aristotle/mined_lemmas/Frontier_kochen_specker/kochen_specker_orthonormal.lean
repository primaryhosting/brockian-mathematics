import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

/-- The four dimensional real Hilbert space in which we work. -/
abbrev KSSpace : Type := EuclideanSpace ℝ (Fin 4)

/-- A vector of `KSSpace` given by its four coordinates. -/

theorem kochen_specker_orthonormal :
    ¬ ∃ v : EuclideanSpace ℝ (Fin 4) → Bool,
        (∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin 4)), 0 < c → v (c • x) = v x) ∧
        ∀ e : Fin 4 → EuclideanSpace ℝ (Fin 4), Orthonormal ℝ e → ∃! i, v (e i) = true := by
  rintro ⟨v, hscale, hbasis⟩
  refine kochen_specker ⟨v, ?_⟩
  intro e hne hor
  set f : Fin 4 → EuclideanSpace ℝ (Fin 4) := fun i => ‖e i‖⁻¹ • e i with hf
  have hpos : ∀ i, 0 < ‖e i‖⁻¹ := fun i => inv_pos.2 (norm_pos_iff.2 (hne i))
  have hvf : ∀ i, v (f i) = v (e i) := fun i => hscale _ _ (hpos i)
  have horth : Orthonormal ℝ f := by
    constructor
    · intro i
      rw [hf]
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hne i))]
    · intro i j hij
      rw [hf]
      simp only [real_inner_smul_left, real_inner_smul_right, hor i j hij]
      ring
  obtain ⟨i, hi, hu⟩ := hbasis f horth
  refine ⟨i, by rwa [hvf] at hi, fun j hj => hu j ?_⟩
  simp only [hvf]
  exact hj

end Frontier

