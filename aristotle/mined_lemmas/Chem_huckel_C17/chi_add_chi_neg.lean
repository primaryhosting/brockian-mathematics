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

lemma chi_add_chi_neg (k : ZMod 17) : chi k + chi (-k) = C17eig k := by
  have h1 : chi k = Complex.exp (((2 * Real.pi * k.val / 17 : ℝ) : ℂ) * I) := by
    rw [chi, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    push_cast
    ring_nf
  have h2 : chi (-k) = (chi k)⁻¹ := AddChar.map_neg_eq_inv _ _
  rw [h2, h1, ← Complex.exp_neg, C17eig, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- The columns of the Fourier matrix are eigenvectors of the adjacency matrix. -/
