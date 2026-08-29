/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace BigOperators

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A *quantum measure* (a finitely additive probability measure on the lattice of closed
subspaces, i.e. on the projection lattice) of a complex Hilbert space `H`.

In finite dimensions every subspace is closed, so we index by `Submodule ℂ H`. -/
structure QuantumMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] where
  /-- The probability assigned to a subspace (equivalently, to its orthogonal projection). -/
  toFun : Submodule ℂ H → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg' : ∀ S, 0 ≤ toFun S
  /-- The whole space has probability one. -/
  total' : toFun ⊤ = 1
  /-- Additivity over orthogonal subspaces. -/
  additive' : ∀ S T : Submodule ℂ H, S ≤ Tᗮ → toFun (S ⊔ T) = toFun S + toFun T

namespace QuantumMeasure

instance : CoeFun (QuantumMeasure H) (fun _ => Submodule ℂ H → ℝ) := ⟨QuantumMeasure.toFun⟩

variable (μ : QuantumMeasure H)


theorem starProjection_sup_apply {S T : Submodule ℂ H} (h : S ≤ Tᗮ) (x : H) :
    (S ⊔ T).starProjection x = S.starProjection x + T.starProjection x := by
  have hS : S.starProjection x ∈ S := (S.orthogonalProjection x).2
  have hT : T.starProjection x ∈ T := (T.orthogonalProjection x).2
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.add_mem_sup hS hT) ?_
  intro w hw
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hw
  have e1 : ⟪x - S.starProjection x, s⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero (K := S) x s hs
  have e2 : ⟪x - T.starProjection x, t⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero (K := T) x t ht
  have e3 : ⟪T.starProjection x, s⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal T s).1 (h hs) _ hT
  have e4 : ⟪S.starProjection x, t⟫_ℂ = 0 :=
    inner_eq_zero_symm.1 ((Submodule.mem_orthogonal T (S.starProjection x)).1 (h hS) t ht)
  have d1 : ⟪x - (S.starProjection x + T.starProjection x), s⟫_ℂ = 0 := by
    rw [show x - (S.starProjection x + T.starProjection x)
      = (x - S.starProjection x) - T.starProjection x by abel, inner_sub_left, e1, e3, sub_zero]
  have d2 : ⟪x - (S.starProjection x + T.starProjection x), t⟫_ℂ = 0 := by
    rw [show x - (S.starProjection x + T.starProjection x)
      = (x - T.starProjection x) - S.starProjection x by abel, inner_sub_left, e2, e4, sub_zero]
  rw [inner_add_right, d1, d2, add_zero]

/-- The trace of a rank-one operator `w ↦ ⟪u, w⟫ • y` is `⟪u, y⟫`. -/
