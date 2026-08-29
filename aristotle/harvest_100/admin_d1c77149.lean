import Mathlib
/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: in Lean 4.28 the `import` command must be the very first command in a file, so the
required header docstring appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Setup

We work with an elliptic curve over `ℚ` presented by an integral Weierstrass model
`W : WeierstrassCurve ℤ` (any elliptic curve over `ℚ` admits such a model).

* The *algebraic rank* is the rank of the Mordell–Weil group `E(ℚ)`, defined as the
  dimension of `ℚ ⊗_ℤ E(ℚ)` over `ℚ`.
* The *analytic rank* is the order of vanishing at `s = 1` of the Hasse–Weil `L`-function,
  where the `L`-function is specified by its Euler product on the half-plane of absolute
  convergence together with analytic continuation to `ℂ`.

Birch–Swinnerton-Dyer asserts that these two numbers agree.
-/

section Rank

/-- The Mordell–Weil group `E(ℚ)` of the elliptic curve given by the integral Weierstrass
model `W`, i.e. the group of rational points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The *algebraic rank* of `W`: the rank of the Mordell–Weil group `E(ℚ)`, defined as
`dim_ℚ (ℚ ⊗_ℤ E(ℚ))`. -/
noncomputable def algebraicRank (W : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ (MordellWeil W))

end Rank

section LFunction

/-- The number of affine points of the reduction of `W` modulo `p`, i.e. of solutions
`(x, y) ∈ 𝔽_p²` of the Weierstrass equation of `W` read modulo `p`. -/
noncomputable def affinePointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card {xy : ZMod p × ZMod p //
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation xy.1 xy.2}

/-- The number of points of the reduction of `W` modulo `p` in the projective plane:
the affine points together with the point at infinity. -/
noncomputable def pointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  affinePointCount W p + 1

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` of `W` at the prime `p`.

At a prime of bad reduction the count `pointCount` includes the unique singular point, so
this expression equals `p - #E_ns(𝔽_p)`, which is the standard `a_p ∈ {1, -1, 0}` in the
split multiplicative, nonsplit multiplicative and additive cases respectively. -/
noncomputable def traceOfFrobenius (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (pointCount W p : ℤ)

/-- The Euler factor of the Hasse–Weil `L`-function of `W` at the prime `p`, evaluated at
`s`; this is the local factor whose inverse appears in the Euler product.  At a prime of
good reduction (`p ∤ Δ`) it is `1 - a_p p^{-s} + p^{1-2s}`, and at a prime of bad
reduction it is `1 - a_p p^{-s}` (with `a_p ∈ {0, ±1}` in that case). -/
noncomputable def eulerFactor (W : WeierstrassCurve ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  if (p : ℤ) ∣ W.Δ then
    1 - (traceOfFrobenius W p : ℂ) * (p : ℂ) ^ (-s)
  else
    1 - (traceOfFrobenius W p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (1 - 2 * s)

/-- `L` is *the* Hasse–Weil `L`-function of the elliptic curve `W`: it is entire, and on the
half-plane of absolute convergence `Re s > 3/2` it is given by the Euler product
`L(E, s) = ∏_p (local factor at p)⁻¹`.

(The Hasse–Weil `L`-function of an elliptic curve over `ℚ` is known to exist and to be
entire, by modularity; we take this predicate as the specification of `L`.) -/
def IsHasseWeilLFunction (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, AnalyticAt ℂ L s) ∧
    ∀ s : ℂ, 3 / 2 < s.re → HasProd (fun p : Nat.Primes => (eulerFactor W p s)⁻¹) (L s)

/-- The *analytic rank* of `W` relative to a function `L`: the order of vanishing of `L`
at `s = 1`, as an element of `ℕ∞` (it is `⊤` if `L` vanishes identically near `1`). -/
noncomputable def analyticRank (L : ℂ → ℂ) : ℕ∞ := analyticOrderAt L 1

end LFunction

/-- **The Birch–Swinnerton-Dyer conjecture (rank part) for the curve `W`**:
the order of vanishing at `s = 1` of the Hasse–Weil `L`-function of `W` equals the rank of
the Mordell–Weil group `E(ℚ)`,
`ord_{s=1} L(E, s) = rank E(ℚ)`. -/
def BSD (W : WeierstrassCurve ℤ) : Prop :=
  ∀ L : ℂ → ℂ, IsHasseWeilLFunction W L → analyticRank L = (algebraicRank W : ℕ∞)

/-- `W` is a *global minimal model*: among all integral Weierstrass models isomorphic to `W`
over `ℚ`, the discriminant of `W` has smallest absolute value.  (Every elliptic curve over
`ℚ` admits such a model, and the Euler product above computes the Hasse–Weil `L`-function
precisely for a global minimal model.) -/
def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ (W' : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ),
    W'.map (Int.castRingHom ℚ) = C • (W.map (Int.castRingHom ℚ)) → |W.Δ| ≤ |W'.Δ|

/-- The full Birch–Swinnerton-Dyer rank conjecture: `BSD` holds for every elliptic curve
over `ℚ`, presented by a global minimal integral Weierstrass model with nonvanishing
discriminant. -/
def BSDConjecture : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → IsGlobalMinimalModel W → BSD W

/-!
## A worked example of the local data

We check the definitions on the curve `y² = x³ + 1` by computing its local point counts and
traces of Frobenius at the primes `5` and `7`.
-/

section Example

/-- The integral Weierstrass model `y² = x³ + 1`. -/
def curve1 : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, 1⟩

/-- The reduction of `y² = x³ + 1` modulo `p` is cut out by `y² = x³ + 1` over `𝔽_p`. -/
theorem curve1_equation_iff (p : ℕ) (x y : ZMod p) :
    (curve1.map (Int.castRingHom (ZMod p))).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 1 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curve1, WeierstrassCurve.map]

theorem affinePointCount_curve1_five : affinePointCount curve1 5 = 5 := by
  have h : ∀ xy : ZMod 5 × ZMod 5,
      (curve1.map (Int.castRingHom (ZMod 5))).toAffine.Equation xy.1 xy.2 ↔
        xy.2 ^ 2 = xy.1 ^ 3 + 1 := fun xy => curve1_equation_iff 5 xy.1 xy.2
  unfold affinePointCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card]
  decide

theorem affinePointCount_curve1_seven : affinePointCount curve1 7 = 11 := by
  have h : ∀ xy : ZMod 7 × ZMod 7,
      (curve1.map (Int.castRingHom (ZMod 7))).toAffine.Equation xy.1 xy.2 ↔
        xy.2 ^ 2 = xy.1 ^ 3 + 1 := fun xy => curve1_equation_iff 7 xy.1 xy.2
  unfold affinePointCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card]
  decide

/-- `a_5 = 0` for `y² = x³ + 1`: the curve is supersingular at `5`. -/
theorem traceOfFrobenius_curve1_five : traceOfFrobenius curve1 5 = 0 := by
  simp [traceOfFrobenius, pointCount, affinePointCount_curve1_five]

/-- `a_7 = -4` for `y² = x³ + 1`. -/
theorem traceOfFrobenius_curve1_seven : traceOfFrobenius curve1 7 = -4 := by
  simp [traceOfFrobenius, pointCount, affinePointCount_curve1_seven]

end Example

/-!
## The reduction

`BSD_statement` below is a Lean-checked reduction of the conjecture to an explicit
factorization statement about the `L`-function, together with the base case `rank = 0`.

Concretely, for an analytic `L`, the assertion `ord_{s=1} L = r` is equivalent to the
existence of a factorization `L(s) = (s-1)^r g(s)` near `s = 1` with `g` analytic and
`g(1) ≠ 0`; and in the base case `r = 0` it is equivalent to the nonvanishing `L(1) ≠ 0`.
-/

/-- Base case of the reduction: for `L` analytic at `1`, the analytic rank is `0` exactly
when `L(1) ≠ 0`. -/
theorem analyticRank_eq_zero_iff {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 1) :
    analyticRank L = 0 ↔ L 1 ≠ 0 :=
  hL.analyticOrderAt_eq_zero

/-- Factorization form of the analytic rank: for `L` analytic at `1` and `n : ℕ`, the
analytic rank of `L` is `n` iff `L(s) = (s-1)^n g(s)` near `s = 1` for some `g` analytic at
`1` with `g(1) ≠ 0`. -/
theorem analyticRank_eq_natCast_iff {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 1) (n : ℕ) :
    analyticRank L = (n : ℕ∞) ↔
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
        ∀ᶠ z in 𝓝 (1 : ℂ), L z = (z - 1) ^ n * g z := by
  simpa [analyticRank, smul_eq_mul] using hL.analyticOrderAt_eq_natCast (n := n)

/-- The half-plane of absolute convergence `{s : Re s > 3/2}` is open. -/
theorem isOpen_halfPlane : IsOpen {s : ℂ | 3 / 2 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- **Uniqueness of the Hasse–Weil `L`-function.**  Any two functions satisfying the
specification `IsHasseWeilLFunction W` are equal: the Euler product determines their common
value on the half-plane of absolute convergence, hence they agree everywhere by the identity
theorem for entire functions. -/
theorem IsHasseWeilLFunction.unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsHasseWeilLFunction W L₁) (h₂ : IsHasseWeilLFunction W L₂) : L₁ = L₂ := by
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  have hev : L₁ =ᶠ[𝓝 (2 : ℂ)] L₂ := by
    filter_upwards [isOpen_halfPlane.mem_nhds hmem] with s hs
    exact (h₁.2 s hs).unique (h₂.2 s hs)
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => h₁.1 s) (fun s _ => h₂.1 s) hev

/-- **Birch–Swinnerton-Dyer: statement and Lean-checked reduction.**

For every integral Weierstrass model `W` of an elliptic curve over `ℚ`:

1. (*Reduction*) BSD for `W` — the equality `ord_{s=1} L(E, s) = rank E(ℚ)` — is equivalent
   to the statement that every Hasse–Weil `L`-function `L` of `W` factors near `s = 1` as
   `L(s) = (s-1)^r g(s)` with `r = rank E(ℚ)` and `g` analytic at `1`, `g(1) ≠ 0`.
2. (*Base case*) If `rank E(ℚ) = 0`, BSD for `W` is equivalent to the nonvanishing
   `L(1) ≠ 0` of the Hasse–Weil `L`-function at the central point.
3. (*Single-`L` form*) Since the Hasse–Weil `L`-function is unique, BSD for `W` is
   equivalent to the equality `ord_{s=1} L = rank E(ℚ)` for any single `L` satisfying the
   specification. -/
theorem BSD_statement (W : WeierstrassCurve ℤ) :
    (BSD W ↔ ∀ L : ℂ → ℂ, IsHasseWeilLFunction W L →
        ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
          ∀ᶠ z in 𝓝 (1 : ℂ), L z = (z - 1) ^ algebraicRank W * g z) ∧
      (algebraicRank W = 0 →
        (BSD W ↔ ∀ L : ℂ → ℂ, IsHasseWeilLFunction W L → L 1 ≠ 0)) ∧
      (∀ L : ℂ → ℂ, IsHasseWeilLFunction W L →
        (BSD W ↔ analyticRank L = (algebraicRank W : ℕ∞))) := by
  refine ⟨⟨fun h L hL => (analyticRank_eq_natCast_iff (hL.1 1) _).mp (h L hL),
      fun h L hL => (analyticRank_eq_natCast_iff (hL.1 1) _).mpr (h L hL)⟩, ?_, ?_⟩
  · intro h0
    constructor
    · intro h L hL
      refine (analyticRank_eq_zero_iff (hL.1 1)).mp ?_
      simpa [h0] using h L hL
    · intro h L hL
      have := (analyticRank_eq_zero_iff (hL.1 1)).mpr (h L hL)
      simpa [h0] using this
  · intro L hL
    refine ⟨fun h => h L hL, fun h L' hL' => ?_⟩
    rwa [← hL.unique hL']

end Frontier

