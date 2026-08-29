import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
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

universe u

namespace Frontier

open scoped InnerProductSpace

/-- A *quantum measure* (a finitely additive probability measure on the lattice of subspaces of
a Hilbert space): a nonnegative function on subspaces, normalized at the whole space, and
additive on pairs of mutually orthogonal subspaces. -/
structure QuantumMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The measure of a subspace. -/
  toFun : Submodule ℂ H → ℝ
  /-- A quantum measure is nonnegative. -/
  nonneg' : ∀ K, 0 ≤ toFun K
  /-- A quantum measure is a probability measure. -/
  normalized' : toFun ⊤ = 1
  /-- A quantum measure is additive on orthogonal subspaces. -/
  additive' : ∀ K L : Submodule ℂ H, K ≤ Lᗮ → toFun (K ⊔ L) = toFun K + toFun L

namespace QuantumMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : CoeFun (QuantumMeasure H) (fun _ => Submodule ℂ H → ℝ) := ⟨QuantumMeasure.toFun⟩


theorem quantumMeasure_of_density {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : H →ₗ[ℂ] H) (hTpos : T.IsPositive)
    (hTtr : LinearMap.trace ℂ H T = 1) :
    ∃ μ : QuantumMeasure H, ∀ K : Submodule ℂ H,
      (μ K : ℂ) = LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)) := by
  classical
  have hid : ((⊤ : Submodule ℂ H).starProjection : H →ₗ[ℂ] H) = LinearMap.id := by
    rw [Submodule.starProjection_top]; rfl
  refine ⟨{ toFun := fun K => RCLike.re (LinearMap.trace ℂ H
              (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)))
            nonneg' := fun K => re_trace_comp_starProjection_nonneg hTpos K
            normalized' := ?_
            additive' := ?_ }, ?_⟩
  · rw [hid, LinearMap.comp_id, hTtr]
    simp
  · intro K L hKL
    have hproj : ((K ⊔ L).starProjection : H →ₗ[ℂ] H)
        = (K.starProjection : H →ₗ[ℂ] H) + (L.starProjection : H →ₗ[ℂ] H) := by
      ext x
      simpa using starProjection_sup_of_orthogonal hKL x
    rw [hproj, LinearMap.comp_add, map_add, map_add]
  · intro K
    exact ofReal_re_trace_comp_starProjection hTpos.1 K

end Frontier

