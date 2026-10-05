/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

noncomputable def affinePointCount (A B : ℤ) (p : ℕ) : ℕ :=
  Nat.card {P : ZMod p × ZMod p // P.2 ^ 2 = P.1 ^ 3 + (A : ZMod p) * P.1 + (B : ZMod p)}

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)`, computed from the affine point count
(the projective point count is the affine one plus the point at infinity). -/
