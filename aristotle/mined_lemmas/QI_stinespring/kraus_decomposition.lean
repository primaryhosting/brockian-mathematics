import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The partial trace over the second (ancilla) factor of a matrix indexed by a product. -/

theorem kraus_decomposition {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hCP : IsCompletelyPositive Φ) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (K : E → Matrix m n ℂ),
      ∀ ρ : Matrix n n ℂ, Φ ρ = ∑ e : E, K e * ρ * (K e)ᴴ := by
  classical
  have hC : (choi Φ).PosSemidef := choi_posSemidef hCP
  obtain ⟨B, hB⟩ : ∃ B : Matrix (n × m) (n × m) ℂ, choi Φ = Bᴴ * B :=
    ⟨CFC.sqrt (choi Φ), by
      rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (choi Φ))).isHermitian.eq,
        CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hC)]⟩
  have hCentry : ∀ (a b : n) (i j : m), Φ (Matrix.single a b 1) i j
      = ∑ e : n × m, (starRingEnd ℂ) (B e (a, i)) * B e (b, j) := by
    intro a b i j
    have := congrFun (congrFun hB (a, i)) (b, j)
    simpa [choi, Matrix.mul_apply, Matrix.conjTranspose_apply] using this
  refine ⟨n × m, inferInstance, inferInstance,
    fun e => Matrix.of fun (i : m) (a : n) => (starRingEnd ℂ) (B e (a, i)), ?_⟩
  intro ρ
  ext i j
  rw [apply_eq_sum_single Φ ρ i j]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    hCentry, Finset.mul_sum, Finset.sum_mul, RCLike.star_def, starRingEnd_self_apply]
  calc ∑ a : n, ∑ b : n, ∑ e : n × m,
        ρ a b * ((starRingEnd ℂ) (B e (a, i)) * B e (b, j))
      = ∑ a : n, ∑ e : n × m, ∑ b : n,
        ρ a b * ((starRingEnd ℂ) (B e (a, i)) * B e (b, j)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ e : n × m, ∑ a : n, ∑ b : n,
        ρ a b * ((starRingEnd ℂ) (B e (a, i)) * B e (b, j)) := Finset.sum_comm
    _ = ∑ e : n × m, ∑ b : n, ∑ a : n,
        (starRingEnd ℂ) (B e (a, i)) * ρ a b * B e (b, j) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq m] in
/-- The Kraus operators of a trace preserving map satisfy the completeness relation. -/
