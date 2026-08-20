import Mathlib
/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command in a file, and a
module docstring `/-! ... -/` may not precede it.  The requested header is therefore placed
immediately after the single `import Mathlib` line, which is as close to the beginning of the
file as the language permits.

Mathlib coverage: as of this Mathlib revision there is no Hasse-Weil L-function of an elliptic
curve, no Mordell-Weil theorem, and no BSD statement (`Mathlib/NumberTheory/LSeries/` covers
only Riemann/Hurwitz zeta and Dirichlet L-functions; `Mathlib/AlgebraicGeometry/EllipticCurve/`
provides the group of nonsingular points `WeierstrassCurve.Affine.Point` but nothing analytic).
So no existing lemma closes or nearly closes this goal; the analytic input is isolated below in
the structure `Frontier.LFunctionDatum`, and the Mordell-Weil theorem appears as the explicit
hypothesis `Module.Finite ℤ (MordellWeil E)`.
-/

open scoped Classical

namespace Frontier

open WeierstrassCurve

/-! ## The Mordell–Weil group and its rank -/

/-- The Mordell–Weil group `E(ℚ)` of an elliptic curve given by an integral Weierstrass
equation `E` over `ℤ`: the group of nonsingular rational points of the base change of `E`
to `ℚ`, in affine coordinates (including the point at infinity). -/
abbrev MordellWeil (E : WeierstrassCurve ℤ) : Type :=
  (E.map (Int.castRingHom ℚ)).toAffine.Point

/-- The algebraic rank of `E`: the rank of the finitely generated abelian group `E(ℚ)`. -/

noncomputable def pointCountMod (E : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card ((E.map (Int.castRingHom (ZMod p))).toAffine.Point)

/-- A *Hasse–Weil L-function datum* for the integral Weierstrass model `E`.

This bundles the analytic object whose existence is (by the modularity theorem) known but is
not available in Mathlib: a function `L` on `ℂ`, analytic at `s = 1`, which on the half-plane
of absolute convergence `Re s > 3/2` is given by the Dirichlet series `∑ a n / n ^ s`, whose
coefficients `a` are the Hasse–Weil coefficients of `E`:

* `a` is multiplicative with `a 1 = 1`;
* at a prime `p` of good reduction (`p ∤ Δ`), `a p = p + 1 - #E(𝔽_p)`, and the coefficients at
  powers of `p` satisfy the recursion coming from the Euler factor
  `(1 - a p * p ^ (-s) + p ^ (1 - 2 s))⁻¹`;
* at a prime `p` of bad reduction (`p ∣ Δ`), the Euler factor is `(1 - a p * p ^ (-s))⁻¹`,
  i.e. `a (p ^ k) = (a p) ^ k`.

These conditions determine `a` uniquely, and (by analytic continuation) determine `L` near
`s = 1` uniquely. -/
structure LFunctionDatum (E : WeierstrassCurve ℤ) where
  /-- The Dirichlet coefficients of the Hasse–Weil L-series of `E`. -/
  a : ℕ → ℂ
  /-- The analytically continued L-function. -/
  L : ℂ → ℂ
  /-- `L` is analytic at `s = 1` (this is part of the modularity theorem). -/
  analyticAt_one : AnalyticAt ℂ L 1
  /-- On the half plane of absolute convergence, `L` is the Hasse–Weil Dirichlet series. -/
  eq_lseries : ∀ s : ℂ, 3 / 2 < s.re → L s = LSeries a s
  /-- Normalisation. -/
  a_one : a 1 = 1
  /-- Multiplicativity. -/
  a_mul : ∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n
  /-- Good primes: `a p = p + 1 - #E(𝔽_p)`. -/
  a_prime_good : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ E.Δ) →
    a p = (p : ℂ) + 1 - (pointCountMod E p : ℂ)
  /-- Good primes: the Euler-factor recursion at prime powers. -/
  a_prime_pow_good : ∀ (p k : ℕ), p.Prime → ¬ ((p : ℤ) ∣ E.Δ) →
    a (p ^ (k + 2)) = a p * a (p ^ (k + 1)) - (p : ℂ) * a (p ^ k)
  /-- Bad primes: `a p = p - #E_ns(𝔽_p)` (`1`, `-1`, `0` for split multiplicative, nonsplit
  multiplicative and additive reduction respectively). -/
  a_prime_bad : ∀ p : ℕ, p.Prime → ((p : ℤ) ∣ E.Δ) →
    a p = (p : ℂ) - (pointCountMod E p : ℂ)
  /-- Bad primes: the Euler factor is degree one. -/
  a_prime_pow_bad : ∀ (p k : ℕ), p.Prime → ((p : ℤ) ∣ E.Δ) →
    a (p ^ k) = a p ^ k

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part) for the integral Weierstrass
model `E` and a Hasse–Weil L-function datum `D` for it:

  `ord_{s = 1} L(E, s) = rank E(ℚ)`.

Here the left-hand side is the order of vanishing of `D.L` at `s = 1`, as an element of `ℕ∞`,
and the right-hand side is the rank of the Mordell–Weil group. -/
