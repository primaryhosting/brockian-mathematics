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

/-!
# Hückel theory for the cyclic polyene C₁₆

The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of an annulene with
16 carbon atoms, up to the usual affine normalisation `α + β x`) has characteristic
polynomial `∏ k < 16, (X - 2 cos (2πk/16))`, so its eigenvalues are exactly the
numbers `2 cos (2πk/16)` for `k = 0, …, 15`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix
`U j k = ω^(jk)`, where `ω = exp (2πi/16)`.
-/

namespace Chem

open Polynomial Matrix Complex

/-- The adjacency (Hückel) matrix of the cycle graph `C₁₆`, over `ℂ`. -/

lemma C16_apply (j l : Fin 16) :
    C16 j l = (if l = j + 1 then (1 : ℂ) else 0) + (if l = j - 1 then 1 else 0) := by
  have hd : ∀ j l : Fin 16, ((SimpleGraph.cycleGraph 16).Adj j l ↔ (l = j + 1 ∨ l = j - 1)) := by
    decide
  have hne : ∀ j : Fin 16, (j + 1 : Fin 16) ≠ j - 1 := by decide
  rw [C16, SimpleGraph.adjMatrix_apply]
  by_cases h1 : l = j + 1
  · have h2 : l ≠ j - 1 := by rw [h1]; exact hne j
    rw [if_pos ((hd j l).mpr (Or.inl h1)), if_pos h1, if_neg h2]; ring
  · by_cases h2 : l = j - 1
    · rw [if_pos ((hd j l).mpr (Or.inr h2)), if_neg h1, if_pos h2]; ring
    · rw [if_neg (fun hc => ((hd j l).mp hc).elim h1 h2), if_neg h1, if_neg h2]
      ring

/-- The Fourier basis diagonalises the circulant matrix `C16`. -/
