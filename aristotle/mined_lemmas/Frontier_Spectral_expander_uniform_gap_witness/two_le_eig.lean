/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/

lemma two_le_eig {k : ℕ} {y : Cube k} (hy : y ≠ 0) : 2 ≤ eig y := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  have hk : 1 ≤ k := i₀.pos
  have hsum : ∑ i : Fin k, sgn (y i) ≤ (k : ℝ) - 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h1 : sgn (y i₀) = -1 := by rw [sgn, if_neg hi₀]
    have h2 : ∑ i ∈ Finset.univ.erase i₀, sgn (y i) ≤ ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => by rw [sgn]; split <;> norm_num)
    have h3 : ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) = (k : ℝ) - 1 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub hk]
      push_cast
      ring
    rw [h1]
    linarith [h2, h3.le, h3.ge]
  rw [eig]
  linarith

