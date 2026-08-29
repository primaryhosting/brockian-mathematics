/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical module docstring is repeated immediately after the imports.)

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
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The arithmetic side: Mordell–Weil rank

An elliptic curve over `ℚ` is presented by an integral Weierstrass model
`W : WeierstrassCurve ℤ` (a global minimal model, see `Frontier.IsGlobalMinimal`).  Its group of
rational points is the Mordell–Weil group `(W.map (Int.castRingHom ℚ)).toAffine.Point`, and its
rank is the dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/

/-- The Mordell–Weil group `E(ℚ)` of the elliptic curve defined by the integral Weierstrass
model `W`. -/
abbrev RationalPoints (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The (algebraic) rank of `E(ℚ)`, defined as `dim_ℚ (ℚ ⊗_ℤ E(ℚ))`.  For a finitely generated
abelian group this is the usual Mordell–Weil rank. -/

def IsGlobalMinimal (W : WeierstrassCurve ℤ) : Prop :=
  ∀ (W' : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ),
    W'.map (Int.castRingHom ℚ) = C • (W.map (Int.castRingHom ℚ)) → W.Δ.natAbs ≤ W'.Δ.natAbs

/-- Data of a Hasse–Weil `L`-function for the elliptic curve given by the global minimal integral
Weierstrass model `W`.

The Dirichlet coefficients `a n` are pinned down by the usual recipe: `a` is multiplicative, its
value at a prime `p` is the trace of Frobenius `a_p` (`Frontier.apCoeff`), at a prime of good
reduction the values on powers of `p` satisfy the standard recursion
`a_{p^{k+2}} = a_p a_{p^{k+1}} - p a_{p^k}`, and at a prime of bad reduction
`a_{p^k} = a_p^k`.  Equivalently, `L(E, s) = ∏_p L_p(E, s)` is the usual Euler product.

The function `L` is required to be entire (this analytic continuation is a theorem, by modularity)
and to be given by the Dirichlet series `∑_{n ≥ 1} a_n n^{-s}` in the region of absolute
convergence `Re s > 3/2`.

By `Frontier.HasseWeilData.L_unique` these requirements determine `L` uniquely, so this is really
"the" Hasse–Weil `L`-function of `E`. -/
structure HasseWeilData (W : WeierstrassCurve ℤ) where
  /-- `W` defines an elliptic curve, i.e. it is nonsingular. -/
  Δ_ne_zero : W.Δ ≠ 0
  /-- `W` is a global minimal model. -/
  minimal : IsGlobalMinimal W
  /-- The Dirichlet coefficients `a_n` of the `L`-series. -/
  a : ArithmeticFunction ℤ
  /-- `a` is multiplicative. -/
  isMultiplicative : a.IsMultiplicative
  /-- At a prime, `a_p` is the trace of Frobenius. -/
  a_prime : ∀ p : ℕ, p.Prime → a p = apCoeff W p
  /-- The Euler factor recursion at a prime of good reduction. -/
  a_prime_pow_good : ∀ (p k : ℕ), p.Prime → ¬ (p : ℤ) ∣ W.Δ →
    a (p ^ (k + 2)) = a p * a (p ^ (k + 1)) - (p : ℤ) * a (p ^ k)
  /-- The Euler factor at a prime of bad reduction. -/
  a_prime_pow_bad : ∀ (p k : ℕ), p.Prime → (p : ℤ) ∣ W.Δ → a (p ^ k) = (a p) ^ k
  /-- The `L`-function. -/
  L : ℂ → ℂ
  /-- `L` is entire. -/
  L_entire : ∀ s : ℂ, AnalyticAt ℂ L s
  /-- On the half plane of absolute convergence, `L` is the Dirichlet series `∑ a_n n^{-s}`. -/
  L_hasSum : ∀ s : ℂ, 3 / 2 < s.re →
    HasSum (fun n : ℕ => (a (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) (L s)

/-- The analytic rank of `E`: the order of vanishing of `L(E, s)` at `s = 1`. -/
