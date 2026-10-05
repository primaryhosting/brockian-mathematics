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

theorem matrix_ext_ip {A B : Matrix n n ℂ}
    (h : ∀ v w, ip v (A *ᵥ w) = ip v (B *ᵥ w)) : A = B := by
  ext p q
  have := h (Pi.single p 1) (Pi.single q 1)
  simpa [ip, Matrix.mulVec, dotProduct, Pi.single_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq] using this

omit [Fintype n] [DecidableEq n] in
