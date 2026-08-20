/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Polynomial

/-- The cyclic shift matrix on `ZMod n`: it sends the standard basis vector `e i` to
`e (i - 1)`, equivalently `(shift n).mulVec v i = v (i + 1)`. -/

noncomputable def shift (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if j = i + 1 then 1 else 0

/-- The adjacency matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is adjacent to `i + 1` and `i - 1`.  In Hückel theory this is the matrix whose
eigenvalues give the π-electron energy levels (in units of `β`, relative to `α`). -/
