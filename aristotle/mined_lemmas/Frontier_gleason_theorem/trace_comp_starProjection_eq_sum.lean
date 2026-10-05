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


lemma trace_comp_starProjection_eq_sum [FiniteDimensional ℂ H] (T : H →ₗ[ℂ] H)
    (K : Submodule ℂ H) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ K) :
    LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H))
      = ∑ i, ⟪((b i : K) : H), T (b i : K)⟫_ℂ := by
  have hcomp : T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)
      = (T ∘ₗ K.subtype) ∘ₗ (K.orthogonalProjection : H →ₗ[ℂ] K) := by
    ext x
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_apply]
  rw [hcomp, LinearMap.trace_comp_comm' (K.orthogonalProjection : H →ₗ[ℂ] K) (T ∘ₗ K.subtype),
    LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply]
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left (b i) (T (b i : K))


/-- The trace of `T` against the projection onto `K` is real when `T` is symmetric, and it is
the sum of the (real) diagonal matrix elements over an orthonormal basis of `K`. -/
