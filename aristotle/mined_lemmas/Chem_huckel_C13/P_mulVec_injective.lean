/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the header
-- above is a plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- The primitive 13-th root of unity `exp(2πi/13)`. -/

lemma P_mulVec_injective {a b : ZMod 13 → ℂ} (hab : P.mulVec a = P.mulVec b) : a = b := by
  have h13 : (13 : ℂ) • a = (13 : ℂ) • b := by
    have h := congrArg (fun v => Q.mulVec v) hab
    simpa [Matrix.mulVec_mulVec, Q_mul_P, Matrix.smul_mulVec, Matrix.one_mulVec] using h
  exact smul_right_injective (ZMod 13 → ℂ) (by norm_num : (13 : ℂ) ≠ 0) h13

/-- **Hückel theory for the cycle `C₁₃`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` if and only if `μ = 2 cos(2πk/13)` for some
`k ∈ {0, 1, …, 12}`. -/
