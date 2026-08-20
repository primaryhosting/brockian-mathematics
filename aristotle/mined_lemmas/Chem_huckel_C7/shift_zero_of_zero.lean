/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of a 7-membered
ring, in units where α = 0 and β = 1): the vertices are `Fin 7` and `i` is adjacent to
`i + 1` and `i - 1`, the arithmetic being modulo 7. -/

lemma shift_zero_of_zero {c : ℂ} {f : Fin 7 → ℂ} (h : ∀ i : Fin 7, f (i + 1) = c * f i)
    (h0 : f 0 = 0) : ∀ i, f i = 0 := by
  have e0 := h 0; have e1 := h 1; have e2 := h 2; have e3 := h 3; have e4 := h 4
  have e5 := h 5
  simp only [Fin.reduceAdd] at e0 e1 e2 e3 e4 e5
  intro i
  fin_cases i <;> simp_all

/-- **Hückel theory for the cycle `C₇`.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the 7-cycle if and only if `μ = 2 cos (2πk/7)` for some
`k ∈ {0, …, 6}`. -/
