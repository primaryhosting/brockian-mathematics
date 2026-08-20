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

lemma shift_cycle {c : ℂ} {f : Fin 7 → ℂ} (h : ∀ i : Fin 7, f (i + 1) = c * f i) :
    f 0 = c ^ 7 * f 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have h5 := h 5; have h6 := h 6
  simp only [Fin.reduceAdd] at h0 h1 h2 h3 h4 h5 h6
  linear_combination h6 + c * h5 + c ^ 2 * h4 + c ^ 3 * h3 + c ^ 4 * h2 + c ^ 5 * h1 + c ^ 6 * h0

/-- A geometric function on the cycle vanishing at `0` vanishes identically. -/
