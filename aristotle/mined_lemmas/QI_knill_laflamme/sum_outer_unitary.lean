/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem sum_outer_unitary {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (g : ι → n → ℂ) :
    ∑ a, outer (∑ i, U i a • g i) = ∑ i, outer (g i) := by
  have hd : ∀ i j, ∑ a, U i a * (starRingEnd ℂ) (U j a) = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun hU i) j
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      eq_comm] using h
  ext p q
  simp only [Matrix.sum_apply, outer, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  have step : ∀ a : ι, (∑ i, U i a * g i p) * (∑ j, (starRingEnd ℂ) (U j a) *
      (starRingEnd ℂ) (g j q))
      = ∑ i, ∑ j, (U i a * (starRingEnd ℂ) (U j a)) * (g i p * (starRingEnd ℂ) (g j q)) := by
    intro a
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ j : ι, ∑ a, (U i a * (starRingEnd ℂ) (U j a)) *
      (g i p * (starRingEnd ℂ) (g j q))
      = (if i = j then 1 else 0) * (g i p * (starRingEnd ℂ) (g j q)) := by
    intro j; rw [← Finset.sum_mul, hd i j]
  rw [Finset.sum_congr rfl fun j _ => this j]
  simp

omit [DecidableEq n] in
