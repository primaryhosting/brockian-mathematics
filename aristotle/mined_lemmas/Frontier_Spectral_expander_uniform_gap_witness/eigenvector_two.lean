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

lemma eigenvector_two {k : ℕ} (i0 : Fin k) :
    ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v := by
  refine ⟨fun x => if x i0 then (1 : ℝ) else -1, ?_, ?_⟩
  · intro hcon
    have hval := congrFun hcon (fun _ => true)
    simp at hval
  · funext x
    rw [lapMatrix_mulVec_hypercube]
    have hterm : ∀ i : Fin k,
        (if flipAt i x i0 then (1 : ℝ) else -1)
          = (if x i0 then (1 : ℝ) else -1)
            - (if i = i0 then 2 * (if x i0 then (1 : ℝ) else -1) else 0) := by
      intro i
      by_cases h : i = i0
      · subst h
        rw [flipAt_apply_self]
        cases hx : x i <;> simp <;> ring
      · rw [flipAt_apply_of_ne (Ne.symm h)]
        simp [h]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
    ring

/-! ## Every nonzero eigenvalue is at least `2` -/

