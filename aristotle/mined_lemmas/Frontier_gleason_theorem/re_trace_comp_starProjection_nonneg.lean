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


lemma re_trace_comp_starProjection_nonneg [FiniteDimensional ℂ H] {T : H →ₗ[ℂ] H}
    (hT : T.IsPositive) (K : Submodule ℂ H) :
    0 ≤ RCLike.re (LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H))) := by
  rw [trace_comp_starProjection_eq_ofReal_sum hT.1 K]
  have hnn : 0 ≤ ∑ i, RCLike.re ⟪((stdOrthonormalBasis ℂ K i : K) : H),
      T (stdOrthonormalBasis ℂ K i : K)⟫_ℂ := by
    refine Finset.sum_nonneg fun i _ => ?_
    have h := hT.2 ((stdOrthonormalBasis ℂ K i : K) : H)
    rwa [hT.1 _ _] at h
  simpa using hnn

end Auxiliary

/-- The *frame property* for a Hilbert space `H`: every quantum measure on `H` is given, on the
one-dimensional subspaces, by a positive operator. -/
