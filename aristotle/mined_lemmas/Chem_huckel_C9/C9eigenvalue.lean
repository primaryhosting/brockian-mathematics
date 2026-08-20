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

noncomputable def C9eigenvalue (k : Fin 9) : ℝ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 9)

/-- A primitive 9-th root of unity. -/
