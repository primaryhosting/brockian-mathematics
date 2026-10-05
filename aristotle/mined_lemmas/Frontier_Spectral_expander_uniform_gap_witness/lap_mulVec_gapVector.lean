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

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → Bool

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

lemma lap_mulVec_gapVector (k : ℕ) (hk : 1 ≤ k) :
    ((hypercube k).lapMatrix ℝ).mulVec (gapVector k hk) = (2 : ℝ) • gapVector k hk := by
  funext x
  have hstep : ∀ i : Fin k, gapVector k hk (cflip x i)
      = gapVector k hk x + (if i = (⟨0, hk⟩ : Fin k) then -(2 * gapVector k hk x) else 0) := by
    intro i
    by_cases h : i = (⟨0, hk⟩ : Fin k)
    · subst h
      rw [if_pos rfl]
      simp only [gapVector, cflip_self]
      cases hx : x (⟨0, hk⟩ : Fin k) <;> norm_num [hx]
    · rw [if_neg h]
      have hc : cflip x i (⟨0, hk⟩ : Fin k) = x (⟨0, hk⟩ : Fin k) := cflip_of_ne x (Ne.symm h)
      simp only [gapVector, hc]
      ring
  have hsum : ∑ i : Fin k, gapVector k hk (cflip x i)
      = k * gapVector k hk x - 2 * gapVector k hk x := by
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (⟨0, hk⟩ : Fin k) (fun _ => -(2 * gapVector k hk x))]
    simp only [Finset.mem_univ, if_pos, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [lap_mulVec_apply, hsum]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q k` (on `2 ^ k` vertices) is exactly `2`; in particular the bound `2` is independent of `k`. -/
