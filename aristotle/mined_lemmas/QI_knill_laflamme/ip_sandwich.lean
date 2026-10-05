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

theorem ip_sandwich {P : Matrix n n ℂ} (hP : IsProj P) {A B : Matrix n n ℂ} (v w : n → ℂ) :
    ip v ((P * Aᴴ * B * P) *ᵥ w) = ip (A *ᵥ (P *ᵥ v)) (B *ᵥ (P *ᵥ w)) := by
  simp only [← mulVec_mulVec]
  rw [ip_mulVec_right P, hP.herm, ip_mulVec_right (Aᴴ), Matrix.conjTranspose_conjTranspose]

omit [DecidableEq ι] in
