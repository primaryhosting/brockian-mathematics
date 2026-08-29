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


lemma sum_span_of_orthonormal {ι : Type*} [DecidableEq ι] (μ : QuantumMeasure H) {v : ι → H}
    (hv : Orthonormal ℂ v) (s : Finset ι) :
    μ (Submodule.span ℂ (v '' s)) = ∑ i ∈ s, μ (Submodule.span ℂ {v i}) := by
  classical
  induction s using Finset.induction with
  | empty => simp [map_bot]
  | insert a s ha ih =>
      have himg : v '' (↑(insert a s) : Set ι) = insert (v a) (v '' (s : Set ι)) := by
        simp [Set.image_insert_eq]
      have horth : Submodule.span ℂ (v '' (s : Set ι)) ≤ (Submodule.span ℂ {v a})ᗮ := by
        rw [Submodule.span_le]
        rintro y ⟨i, hi, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
        refine inner_eq_zero_symm.mp (hv.2 ?_)
        rintro rfl
        exact ha hi
      rw [himg, Submodule.span_insert, sup_comm, μ.additive horth, Finset.sum_insert ha, ih]
      ring

end QuantumMeasure

section Auxiliary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The image in `H` of an orthonormal basis of a subspace `K` spans `K`. -/
