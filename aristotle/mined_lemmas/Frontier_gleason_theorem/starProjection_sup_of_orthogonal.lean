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


lemma starProjection_sup_of_orthogonal [FiniteDimensional ℂ H] {K L : Submodule ℂ H} (h : K ≤ Lᗮ)
    (x : H) : (K ⊔ L).starProjection x = K.starProjection x + L.starProjection x := by
  set p := K.starProjection x with hp
  set q := L.starProjection x with hq
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.add_mem_sup (K.starProjection_apply_mem x) (L.starProjection_apply_mem x)) ?_
  intro w hw
  rw [Submodule.mem_sup] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  have h1 : ⟪x - p, a⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (K.sub_starProjection_mem_orthogonal x a ha)
  have h2 : ⟪x - q, b⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (L.sub_starProjection_mem_orthogonal x b hb)
  have hqa : ⟪q, a⟫_ℂ = 0 := (h ha) q (L.starProjection_apply_mem x)
  have hpb : ⟪p, b⟫_ℂ = 0 := inner_eq_zero_symm.mp ((h (K.starProjection_apply_mem x)) b hb)
  have key1 : ⟪x - p - q, a⟫_ℂ = 0 := by rw [inner_sub_left, h1, hqa]; ring
  have key2 : ⟪x - p - q, b⟫_ℂ = 0 := by
    rw [show x - p - q = x - q - p from by abel, inner_sub_left, h2, hpb]; ring
  rw [show x - (p + q) = x - p - q from by abel, inner_add_right, key1, key2]
  ring

/-- For a symmetric operator `T`, the diagonal matrix elements `⟪x, T x⟫` are real. -/
