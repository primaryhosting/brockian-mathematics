/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring before `import`; the required header is repeated verbatim
-- as the module docstring immediately below the import.)

import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open scoped TensorProduct

/-! ## The arithmetic side: Mordell–Weil rank -/

/-- The Mordell–Weil group `E(ℚ)` of an integral Weierstrass model `W`, i.e. the group of
rational nonsingular points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the dimension of `ℚ ⊗ℤ E(ℚ)` over `ℚ`.
For a finitely generated abelian group this is exactly the rank of its free part. -/

def convergenceHalfPlane : Set ℂ := {s : ℂ | 3 / 2 < s.re}

/-- `L` is *the* Hasse–Weil `L`-function of the integral Weierstrass model `W`: it is entire
(this is the content of the modularity theorem) and on the half-plane `Re s > 3/2` it is given
by the Euler product `∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})⁻¹`. -/
structure IsHasseWeilL (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop where
  /-- `L` is entire, i.e. analytic at every point of `ℂ`. -/
  entire : ∀ s : ℂ, AnalyticAt ℂ L s
  /-- On `Re s > 3/2`, `L s` is the value of the Hasse–Weil Euler product. -/
  hasProd : ∀ s ∈ convergenceHalfPlane, HasProd (fun p : Nat.Primes => eulerFactor W p s) (L s)

/-- `W` is a global minimal Weierstrass model of the elliptic curve it defines over `ℚ`:
among all integral models of the same curve it has discriminant of least absolute value. -/
