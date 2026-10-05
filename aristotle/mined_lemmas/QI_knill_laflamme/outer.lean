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

def outer (v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec v (star v)

/-- `P` is an orthogonal projector. -/
structure IsProj (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P

/-- The code with projector `P` is *correctable* for the error set `E` if there is a
recovery quantum channel, given by Kraus operators `R k` with `∑ k, (R k)ᴴ * (R k) = 1`,
whose composition with the error channel `ρ ↦ ∑ i, E i * ρ * (E i)ᴴ` acts as the identity
(up to the trace factor) on every pure state of the code space. -/
