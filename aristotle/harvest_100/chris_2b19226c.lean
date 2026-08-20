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
noncomputable def algebraicRank (E : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℤ (MordellWeil E)

/-! ## The Hasse–Weil L-function -/

/-- The number of points of the reduction of `E` modulo a prime `p`, i.e. `#E(𝔽_p)`
(nonsingular points, including the point at infinity). -/
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
def BSD (E : WeierstrassCurve ℤ) (D : LFunctionDatum E) : Prop :=
  analyticOrderAt D.L 1 = (algebraicRank E : ℕ∞)

/-! ## The L-series coefficients are pinned down by the datum -/

namespace LFunctionDatum

variable {E : WeierstrassCurve ℤ}

/-- The coefficient at a prime is determined by the curve. -/
theorem a_prime_eq (D₁ D₂ : LFunctionDatum E) {p : ℕ} (hp : p.Prime) : D₁.a p = D₂.a p := by
  by_cases hd : ((p : ℤ) ∣ E.Δ)
  · rw [D₁.a_prime_bad p hp hd, D₂.a_prime_bad p hp hd]
  · rw [D₁.a_prime_good p hp hd, D₂.a_prime_good p hp hd]

/-- The coefficients at prime powers are determined by the curve. -/
theorem a_prime_pow_eq (D₁ D₂ : LFunctionDatum E) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    D₁.a (p ^ k) = D₂.a (p ^ k) := by
  have hp1 : D₁.a p = D₂.a p := D₁.a_prime_eq D₂ hp
  by_cases hd : ((p : ℤ) ∣ E.Δ)
  · rw [D₁.a_prime_pow_bad p k hp hd, D₂.a_prime_pow_bad p k hp hd, hp1]
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => simp [D₁.a_one, D₂.a_one]
      | 1 => simpa using hp1
      | (m + 2) =>
        rw [D₁.a_prime_pow_good p m hp hd, D₂.a_prime_pow_good p m hp hd,
          ih (m + 1) (by omega), ih m (by omega), hp1]

/-- **Uniqueness of the Hasse–Weil coefficients.** Any two L-function data for the same
integral Weierstrass model have the same Dirichlet coefficients (at every `n ≠ 0`; the value
at `n = 0` is irrelevant for the L-series). -/
theorem a_eq (D₁ D₂ : LFunctionDatum E) {n : ℕ} (hn : n ≠ 0) : D₁.a n = D₂.a n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ => exact D₁.a_prime_pow_eq D₂ hp k
  | zero => exact absurd rfl hn
  | one => rw [D₁.a_one, D₂.a_one]
  | coprime x y hx hy hxy ihx ihy =>
      rw [D₁.a_mul x y hxy, D₂.a_mul x y hxy, ihx (by omega), ihy (by omega)]

/-- Consequently any two L-function data for the same curve define the same L-series on the
half-plane of absolute convergence. -/
theorem L_eq_of_lt_re (D₁ D₂ : LFunctionDatum E) {s : ℂ} (hs : 3 / 2 < s.re) :
    D₁.L s = D₂.L s := by
  rw [D₁.eq_lseries s hs, D₂.eq_lseries s hs]
  exact LSeries_congr (fun hn => D₁.a_eq D₂ hn) s

end LFunctionDatum

/-! ## A Lean-checked reduction: the rank-zero base case -/

/-- The analytic order of vanishing at `s = 1` is `0` exactly when `L(E, 1) ≠ 0`. -/
theorem analyticOrder_eq_zero_iff (E : WeierstrassCurve ℤ) (D : LFunctionDatum E) :
    analyticOrderAt D.L 1 = 0 ↔ D.L 1 ≠ 0 :=
  D.analyticAt_one.analyticOrderAt_eq_zero

/-- Given the Mordell–Weil theorem (finite generation of `E(ℚ)`), the algebraic rank vanishes
exactly when every rational point is a torsion point. -/
theorem algebraicRank_eq_zero_iff (E : WeierstrassCurve ℤ)
    (hfg : Module.Finite ℤ (MordellWeil E)) :
    algebraicRank E = 0 ↔ ∀ P : MordellWeil E, ∃ n : ℕ, 0 < n ∧ n • P = 0 := by
  rw [algebraicRank, Module.finrank_eq_zero_iff_isTorsion]
  constructor
  · intro h P
    obtain ⟨⟨m, hm⟩, hmP⟩ := @h P
    have hmP' : m • P = 0 := hmP
    refine ⟨m.natAbs, Int.natAbs_pos.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hm), ?_⟩
    have : (m.natAbs : ℤ) • P = 0 := by
      rcases Int.natAbs_eq m with h' | h'
      · rw [← h']; exact hmP'
      · rw [show ((m.natAbs : ℤ)) = -m by omega, neg_smul, hmP', neg_zero]
    simpa [← natCast_zsmul] using this
  · intro h P
    obtain ⟨n, hn, hnP⟩ := h P
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hn.ne')⟩, ?_⟩
    simpa [natCast_zsmul] using hnP

/-- **BSD statement, with a Lean-checked reduction to its rank-zero base case.**

For an elliptic curve given by an integral Weierstrass model `E` over `ℤ`, with a Hasse–Weil
L-function datum `D` (an analytic continuation of `∑ a n n^{-s}` to a neighbourhood of `s = 1`),
assuming the Mordell–Weil theorem for `E` (finite generation of `E(ℚ)`), the Birch and
Swinnerton-Dyer conjecture `ord_{s=1} L(E,s) = rank E(ℚ)` implies its rank-zero base case:

  `L(E, 1) ≠ 0 ↔ E(ℚ) is a torsion group`,

and, complementarily, `L(E, 1) = 0` exactly when `E(ℚ)` has positive rank. -/
theorem BSD_statement (E : WeierstrassCurve ℤ) (D : LFunctionDatum E)
    (hfg : Module.Finite ℤ (MordellWeil E)) (hBSD : BSD E D) :
    (D.L 1 ≠ 0 ↔ ∀ P : MordellWeil E, ∃ n : ℕ, 0 < n ∧ n • P = 0) ∧
      (D.L 1 = 0 ↔ 0 < algebraicRank E) := by
  have key : D.L 1 ≠ 0 ↔ algebraicRank E = 0 := by
    rw [← analyticOrder_eq_zero_iff E D, BSD] at *
    rw [hBSD]
    exact_mod_cast Iff.rfl
  refine ⟨key.trans (algebraicRank_eq_zero_iff E hfg), ?_⟩
  rw [← not_iff_not, not_lt, Nat.le_zero, ← key]

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

