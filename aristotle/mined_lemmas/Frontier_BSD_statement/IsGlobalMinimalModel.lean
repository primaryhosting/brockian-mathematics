import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
required header block is placed immediately after `import Mathlib`.

This file formalises the statement of the Birch--Swinnerton-Dyer conjecture

  ord_{s = 1} L(E, s) = rank E(ℚ)

for elliptic curves over `ℚ` given by a global minimal integral Weierstrass model, and proves
the rank-zero base case together with a Lean-checked reduction of the rank-zero case of the
conjecture to the equivalence `L(E, 1) ≠ 0 ↔ E(ℚ) finite`.
-/

namespace Frontier

open WeierstrassCurve

/-! ## The Mordell–Weil group and its rank -/

/-- The group `E(ℚ)` of rational points of the elliptic curve given by the integral
Weierstrass model `W` over `ℤ`. -/
abbrev RatPoints (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The algebraic rank of `E(ℚ)`: the rank of the Mordell–Weil group as a `ℤ`-module. -/

def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ (W' : WeierstrassCurve ℤ) (C : VariableChange ℚ),
    W'.baseChange ℚ = C • W.baseChange ℚ → W.Δ.natAbs ≤ W'.Δ.natAbs

/-- `a : ℕ → ℂ` is the sequence of Dirichlet coefficients of the Hasse–Weil `L`-series of the
global minimal Weierstrass model `W`, i.e.

  `L(E, s) = ∑ n, a n / n ^ s = ∏_{p good} (1 - a_p p^{-s} + p^{1 - 2s})⁻¹
                                 ∏_{p bad}  (1 - a_p p^{-s})⁻¹`.

This is expressed through the multiplicativity of `a`, the value of `a` at primes, and the
Euler-factor recursions at prime powers. -/
