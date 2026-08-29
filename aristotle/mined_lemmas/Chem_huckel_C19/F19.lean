import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

noncomputable def F19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun i j => omega19 ^ (i.val * j.val)

/-- The inverse discrete Fourier transform matrix of size 19. -/
