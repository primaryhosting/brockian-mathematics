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


lemma inner_self_ofReal_re {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) (x : H) :
    ((RCLike.re ⟪x, T x⟫_ℂ : ℝ) : ℂ) = ⟪x, T x⟫_ℂ := by
  have h : (starRingEnd ℂ) ⟪x, T x⟫_ℂ = ⟪x, T x⟫_ℂ := by
    rw [inner_conj_symm]; exact hT x x
  simpa using Complex.conj_eq_iff_re.mp h

/-- The trace of `T` composed with the orthogonal projection onto `K` is computed by summing
the diagonal matrix elements of `T` over an orthonormal basis of `K`. -/
