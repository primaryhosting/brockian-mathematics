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
noncomputable def mordellWeilRank (W : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℚ (ℚ ⊗[ℤ] RationalPoints W)

/-! ## The analytic side: the Hasse–Weil `L`-function -/

/-- The number of `𝔽_p`-points (including the point at infinity) of the reduction of the integral
Weierstrass model `W` modulo `p`.  Note that `WeierstrassCurve.Affine.Point` only comprises the
*nonsingular* points, so at a prime of bad reduction this counts the smooth part
`Ẽ_ns(𝔽_p)` of the reduction. -/
noncomputable def reductionCard (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card ((W.map (Int.castRingHom (ZMod p))).toAffine.Point)

/-- The `p`-th Hasse–Weil coefficient `a_p` of a global minimal model `W`.

* at a prime `p` of good reduction (`p ∤ Δ`) this is `a_p = p + 1 - #Ẽ(𝔽_p)`;
* at a prime `p` of bad reduction (`p ∣ Δ`) this is `a_p = p - #Ẽ_ns(𝔽_p)`, which equals `1`
  for split multiplicative reduction, `-1` for nonsplit multiplicative reduction and `0` for
  additive reduction. -/
noncomputable def apCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (if (p : ℤ) ∣ W.Δ then (p : ℤ) else (p : ℤ) + 1) - (reductionCard W p : ℤ)

/-- `W` is a global minimal Weierstrass model: among all integral Weierstrass models isomorphic
to `W` over `ℚ`, its discriminant has minimal absolute value. -/
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
noncomputable def analyticRank {W : WeierstrassCurve ℤ} (D : HasseWeilData W) : ℕ∞ :=
  analyticOrderAt D.L 1

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part) for the elliptic curve given by the
global minimal integral Weierstrass model `W`: the Hasse–Weil `L`-function of `E` exists (it
admits an analytic continuation to `s = 1`) and
`ord_{s = 1} L(E, s) = rank E(ℚ)`. -/
def BSD (W : WeierstrassCurve ℤ) : Prop :=
  Nonempty (HasseWeilData W) ∧
    ∀ D : HasseWeilData W, analyticRank D = (mordellWeilRank W : ℕ∞)

/-! ## Auxiliary results -/

/-- A finite abelian group has vanishing rationalisation. -/
theorem finrank_rat_tensor_eq_zero (M : Type) [AddCommGroup M] [Finite M] :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = 0 := by
  have : Subsingleton (ℚ ⊗[ℤ] M) := by
    constructor
    intro x y
    suffices h : ∀ z : ℚ ⊗[ℤ] M, z = 0 by rw [h x, h y]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul q m =>
        have hcard : (Nat.card M) • m = 0 := card_nsmul_eq_zero'
        have h1 : q = ((Nat.card M : ℤ)) • (q / (Nat.card M : ℚ)) := by
          have hne : ((Nat.card M : ℚ)) ≠ 0 := by
            simpa using (Nat.card_pos (α := M)).ne'
          push_cast [zsmul_eq_mul]
          field_simp
        rw [h1, TensorProduct.smul_tmul, natCast_zsmul, hcard, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact Module.finrank_zero_of_subsingleton

/-- If `E(ℚ)` is finite then the Mordell–Weil rank is `0`. -/
theorem mordellWeilRank_eq_zero_of_finite (W : WeierstrassCurve ℤ)
    (h : Finite (RationalPoints W)) : mordellWeilRank W = 0 :=
  finrank_rat_tensor_eq_zero _

/-- The Dirichlet coefficients of any two Hasse–Weil data for `W` agree on prime powers. -/
theorem HasseWeilData.a_prime_pow_eq {W : WeierstrassCurve ℤ} (D₁ D₂ : HasseWeilData W)
    (p : ℕ) (hp : p.Prime) (k : ℕ) : D₁.a (p ^ k) = D₂.a (p ^ k) := by
  by_cases hbad : (p : ℤ) ∣ W.Δ
  · rw [D₁.a_prime_pow_bad p k hp hbad, D₂.a_prime_pow_bad p k hp hbad,
      D₁.a_prime p hp, D₂.a_prime p hp]
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => simp [D₁.isMultiplicative.map_one, D₂.isMultiplicative.map_one]
      | 1 => simpa using (D₁.a_prime p hp).trans (D₂.a_prime p hp).symm
      | (n + 2) =>
        rw [D₁.a_prime_pow_good p n hp hbad, D₂.a_prime_pow_good p n hp hbad,
          ih (n + 1) (by omega), ih n (by omega), D₁.a_prime p hp, D₂.a_prime p hp]

/-- The Dirichlet coefficients are determined by `W`. -/
theorem HasseWeilData.a_eq {W : WeierstrassCurve ℤ} (D₁ D₂ : HasseWeilData W) : D₁.a = D₂.a :=
  (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers D₁.a D₁.isMultiplicative D₂.a
      D₂.isMultiplicative).2
    fun p i hp => D₁.a_prime_pow_eq D₂ p hp i

/-- **The Hasse–Weil `L`-function is unique**: the defining properties (Euler product on
`Re s > 3/2` together with entirety) determine `L` completely.  In particular the analytic rank
`ord_{s=1} L(E, s)` is a well-defined invariant of the curve. -/
theorem HasseWeilData.L_unique {W : WeierstrassCurve ℤ} (D₁ D₂ : HasseWeilData W) :
    D₁.L = D₂.L := by
  have hcoeff : D₁.a = D₂.a := D₁.a_eq D₂
  -- The two `L`-functions agree on the half plane of absolute convergence.
  have hhalf : ∀ s : ℂ, 3 / 2 < s.re → D₁.L s = D₂.L s := by
    intro s hs
    have h₁ := D₁.L_hasSum s hs
    have h₂ := D₂.L_hasSum s hs
    rw [hcoeff] at h₁
    exact h₁.unique h₂
  -- The half plane is open, so they are eventually equal near `s = 2`.
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]
    norm_num
  have hev : D₁.L =ᶠ[nhds (2 : ℂ)] D₂.L :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) fun s hs => hhalf s hs
  -- Analytic continuation from a neighbourhood of `2` to all of `ℂ`.
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (f := D₁.L) (g := D₂.L) (U := Set.univ)
    (fun z _ => D₁.L_entire z) (fun z _ => D₂.L_entire z) isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  funext z
  exact this (Set.mem_univ z)

/-! ## The Birch and Swinnerton-Dyer statement -/

/-- **Birch–Swinnerton-Dyer**, formalized statement together with a Lean-checked reduction.

For every global minimal integral Weierstrass model `W` of an elliptic curve `E / ℚ`
(the hypotheses of minimality and nonsingularity being part of `Frontier.HasseWeilData`):

1. *Well-posedness.*  Any two Hasse–Weil data for `W` have the same `L`-function; hence the
   analytic rank `ord_{s=1} L(E, s)` is a genuine invariant of `E`.
2. *Reduction to a single `L`-function.*  BSD for `E`, i.e. `ord_{s=1} L(E, s) = rank E(ℚ)`,
   holds if and only if the equality holds for one (equivalently, any) choice of Hasse–Weil data.
3. *Base case (rank zero).*  If `E(ℚ)` is finite — so that `rank E(ℚ) = 0` — then BSD for `E`
   is equivalent to the non-vanishing `L(E, 1) ≠ 0`.

The full conjecture (that the equality in (2) always holds) remains open; what is proved here is
the formal statement, its well-posedness, and the rank-zero reduction. -/
theorem BSD_statement (W : WeierstrassCurve ℤ) :
    (∀ D₁ D₂ : HasseWeilData W, D₁.L = D₂.L ∧ analyticRank D₁ = analyticRank D₂) ∧
    (∀ D : HasseWeilData W, BSD W ↔ analyticRank D = (mordellWeilRank W : ℕ∞)) ∧
    (∀ D : HasseWeilData W, Finite (RationalPoints W) → (BSD W ↔ D.L 1 ≠ 0)) := by
  have key : ∀ D₁ D₂ : HasseWeilData W, analyticRank D₁ = analyticRank D₂ := by
    intro D₁ D₂
    unfold analyticRank
    rw [D₁.L_unique D₂]
  have main : ∀ D : HasseWeilData W, (BSD W ↔ analyticRank D = (mordellWeilRank W : ℕ∞)) := by
    intro D
    constructor
    · intro h
      exact h.2 D
    · intro h
      exact ⟨⟨D⟩, fun D' => (key D' D).trans h⟩
  refine ⟨fun D₁ D₂ => ⟨D₁.L_unique D₂, key D₁ D₂⟩, main, ?_⟩
  · intro D hfin
    have hrank : mordellWeilRank W = 0 := mordellWeilRank_eq_zero_of_finite W hfin
    rw [main D, hrank]
    simpa [analyticRank] using (D.L_entire 1).analyticOrderAt_eq_zero

end Frontier

