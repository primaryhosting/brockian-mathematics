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

theorem scalar_of_unit_scalar {T : Matrix n n ℂ} {v : n → ℂ} {r c : ℂ} (hr : r ≠ 0)
    (h : T *ᵥ (r • v) = c • (r • v)) : T *ᵥ v = c • v := by
  rw [mulVec_smul, smul_comm] at h
  exact smul_right_injective _ hr h

omit [DecidableEq n] in
/-- A matrix which acts as a scalar on every unit vector of the code space acts as a
single scalar on the whole code space. -/
