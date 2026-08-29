/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

noncomputable def dftMatInv : Matrix (ZMod 20) (ZMod 20) ℂ :=
  Matrix.of fun k j => (20 : ℂ)⁻¹ * e (-(k * j))

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/20)`. -/
