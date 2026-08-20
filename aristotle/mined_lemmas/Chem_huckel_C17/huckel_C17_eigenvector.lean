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

theorem huckel_C17_eigenvector (k : ZMod 17) :
    C17adj.mulVec (fun j => chi (j * k)) = C17eig k • (fun j => chi (j * k)) := by
  funext i
  have h := congrFun (congrFun C17adj_mul_C17F i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simpa [Matrix.mulVec, dotProduct, C17F, Pi.smul_apply, smul_eq_mul, mul_comm] using h

end Chem

