import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier.Spectral

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

lemma sum_sq_pos {n : ℕ} [NeZero n] {v : ZMod n → ℝ} (hv0 : v ≠ 0) :
    0 < ∑ i : ZMod n, (v i) ^ 2 := by
  rcases Function.ne_iff.mp hv0 with ⟨i, hi⟩
  refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  have hvi : v i ≠ 0 := by simpa using hi
  positivity

/-- **Fiedler value of the cycle graph.**
For `n ≥ 3`, the algebraic connectivity of the cycle `C n` — the least eigenvalue of the
Laplacian `cycleLaplacian n` among eigenvectors orthogonal to the all-ones vector — equals
`2 - 2 * cos (2π/n)`. -/
