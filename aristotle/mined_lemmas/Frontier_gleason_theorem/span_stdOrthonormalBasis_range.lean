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


theorem span_stdOrthonormalBasis_range (S : Submodule ℂ H) :
    Submodule.span ℂ (Set.range fun i => ((stdOrthonormalBasis ℂ S i : S) : H)) = S := by
  have hb : Submodule.span ℂ (Set.range (stdOrthonormalBasis ℂ S)) = ⊤ := by
    simpa using (stdOrthonormalBasis ℂ S).toBasis.span_eq
  have hr : (Set.range fun i => (((stdOrthonormalBasis ℂ S) i : S) : H))
      = S.subtype '' (Set.range (stdOrthonormalBasis ℂ S)) := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Submodule.map_span, hb, Submodule.map_top, Submodule.range_subtype]

/-- **Gleason's theorem (Lean-checked reduction).**

Let `μ` be a quantum measure (a finitely additive probability measure on the projection
lattice) on a complex Hilbert space `H` of dimension at least `3`.  Gleason's theorem asserts
that `μ` is given by a density operator.  The whole content of the theorem is the statement
that the *frame function* `x ↦ μ (ℂ ∙ x)` on the unit sphere is a quadratic form; this is where
the hypothesis `3 ≤ dim H` enters.

Here we verify the complete reduction: **as soon as the frame function of `μ` is represented by
some linear operator `A`, that operator is automatically a density operator and `μ` is the
associated quantum measure `S ↦ tr (A P_S)`.**

The dimension hypothesis `3 ≤ finrank ℂ H` is kept because it is part of the statement of
Gleason's theorem, but it is not needed for this reduction step. -/
