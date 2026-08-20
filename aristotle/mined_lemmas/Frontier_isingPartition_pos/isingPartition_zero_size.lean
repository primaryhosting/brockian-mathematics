import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The two-dimensional Ising model on a periodic square lattice -/

/-- The real spin value attached to a Boolean spin variable: `true ↦ +1`, `false ↦ -1`. -/

theorem isingPartition_zero_size (K : ℝ) :
    isingPartition 0 K = 2 * Real.exp (2 * K) := by
  have hb : ∀ σ : Config 0, bondSum σ = 2 := by
    intro σ
    rw [bondSum, Fin.sum_univ_one, Fin.sum_univ_one, show (0 + 1 : Fin 1) = 0 from rfl]
    rcases h : σ (0, 0) with _ | _ <;> norm_num [spin, h]
  simp only [isingPartition, hb]
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (Config 0) = 2 := by decide
  rw [hcard, nsmul_eq_mul, mul_comm K 2]
  norm_num

/-! ## Exact evaluation at infinite temperature (`K = 0`) -/

/-- At infinite temperature all `2^{N²}` configurations have equal weight. -/
