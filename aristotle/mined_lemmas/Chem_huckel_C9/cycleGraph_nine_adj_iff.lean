import Mathlib

/-!
# Hückel theory for the cycle C₉

The adjacency matrix of the cycle graph `C₉` is diagonalized by the discrete Fourier
(Vandermonde) matrix built from a primitive 9-th root of unity.  Consequently its
characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/9))`, and its spectrum is
exactly `{2 cos (2πk/9) : k = 0, …, 8}` — the Hückel energy levels of a nine-membered
conjugated ring.
-/

open Polynomial Matrix SimpleGraph Complex

namespace Chem

/-- The adjacency matrix of the cycle graph `C₉`, over `ℂ`. -/

theorem cycleGraph_nine_adj_iff (i j : Fin 9) :
    (cycleGraph 9).Adj i j ↔ (j = i + 1 ∨ i = j + 1) := by
  revert i j
  decide

/-- The Fourier vector `i ↦ ω^{ki}` is an eigenvector of the adjacency matrix of `C₉`
with eigenvalue `2 cos (2πk/9)`. -/
