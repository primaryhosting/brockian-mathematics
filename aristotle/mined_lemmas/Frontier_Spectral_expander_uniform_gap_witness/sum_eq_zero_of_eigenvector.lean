/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Frontier.Spectral

open Finset Matrix

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `Fin k → Bool`. -/

lemma sum_eq_zero_of_eigenvector {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) {v : (Fin k → Bool) → ℝ}
    (hv : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) : ∑ x : Fin k → Bool, v x = 0 := by
  have hflip : ∀ i : Fin k, ∑ x : Fin k → Bool, v (flipAt i x) = ∑ x : Fin k → Bool, v x :=
    fun i => Fintype.sum_equiv (Function.Involutive.toPerm (flipAt i) (flipAt_flipAt i)) _ _
      (fun _ => rfl)
  have key : ∑ x : Fin k → Bool, ((hypercube k).lapMatrix ℝ *ᵥ v) x = 0 := by
    simp only [lapMatrix_mulVec_hypercube]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
    simp only [hflip, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hv] at key
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at key
  exact (mul_eq_zero.mp key).resolve_left hμ

