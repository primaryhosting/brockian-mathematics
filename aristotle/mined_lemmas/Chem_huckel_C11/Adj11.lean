/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring; the header above is
-- repeated below as the module docstring.)
import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard additive character of `ZMod 11`, `x ↦ exp (2πI x / 11)`. -/
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod 11) ℂ)

/-- The Hückel eigenvalues of the cycle `C₁₁`. -/

noncomputable def Adj11 : Matrix (ZMod 11) (ZMod 11) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The (unnormalised) discrete Fourier matrix. -/
