/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the same header is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Matrix Complex

/-- The adjacency matrix of the cycle graph `C₁₇` (the Hückel matrix of the cyclic
polyene, in units where the diagonal Coulomb integral is `0` and the resonance
integral is `1`), with vertices indexed by `ZMod 17`: `i` and `j` are adjacent iff
they differ by `1`. -/

lemma det_sub_C17adj (μ : ℂ) :
    (Matrix.diagonal (fun _ : ZMod 17 => μ) - C17adj).det = ∏ k : ZMod 17, (μ - C17eig k) := by
  have hcomm : (Matrix.diagonal (fun _ : ZMod 17 => μ)) * C17F
      = C17F * (Matrix.diagonal (fun _ : ZMod 17 => μ)) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have key : (Matrix.diagonal (fun _ : ZMod 17 => μ) - C17adj) * C17F
      = C17F * Matrix.diagonal (fun k : ZMod 17 => μ - C17eig k) := by
    rw [Matrix.sub_mul, hcomm, C17adj_mul_C17F, ← Matrix.mul_sub]
    congr 1
    rw [← Matrix.diagonal_sub]
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h2
  exact mul_right_cancel₀ det_C17F_ne_zero (by rw [h2]; ring :
    (Matrix.diagonal (fun _ : ZMod 17 => μ) - C17adj).det * C17F.det
      = (∏ k : ZMod 17, (μ - C17eig k)) * C17F.det)

/-- **Hückel theory for the cycle `C₁₇`.** The spectrum of the adjacency matrix of the
cycle graph on 17 vertices consists exactly of the numbers `2 cos (2πk/17)`,
for `k = 0, 1, …, 16`. -/
