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

namespace Frontier

open Filter Topology WeierstrassCurve

/-!
## Setup

An elliptic curve over `ℚ` is presented by an integral Weierstrass model `W : WeierstrassCurve ℤ`
with nonvanishing discriminant.  We formalize:

* the *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`;
* the local data (`a_p`, `ε_p`) and the Euler factors of the Hasse–Weil `L`-function of `W`;
* the predicate `IsHasseWeilLFunction W L` saying that the entire function `L` is the analytic
  continuation of the Hasse–Weil `L`-series of `W`;
* the Birch–Swinnerton-Dyer equality `ord_{s=1} L(E, s) = rank E(ℚ)`.
-/

/-- The Mordell–Weil group `E(ℚ)` of the Weierstrass model `W` over `ℤ`, namely the group of
nonsingular rational points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`, defined as the
dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/
noncomputable def algebraicRank (W : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ (MordellWeil W))

/-- The number of nonsingular `𝔽_p`-points (including the point at infinity) of the reduction of
`W` modulo `p`.  For a prime `p` of good reduction this is `#E(𝔽_p)`, and for a prime of bad
reduction it is `#E^{ns}(𝔽_p)`. -/
noncomputable def reductionPointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card ((W.map (Int.castRingHom (ZMod p))).toAffine.Point)

/-- `W` has good reduction at `p` when `p` does not divide the discriminant of `W`.  (This is the
usual notion when `W` is a global minimal model.) -/
def HasGoodReduction (W : WeierstrassCurve ℤ) (p : ℕ) : Prop := ¬ (p : ℤ) ∣ W.Δ

/-- The coefficient `ε_p`, equal to `1` at primes of good reduction and `0` at primes of bad
reduction. -/
noncomputable def epsilonCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  if HasGoodReduction W p then 1 else 0

/-- The trace of Frobenius `a_p`, characterized by `#E^{ns}(𝔽_p) = p + ε_p - a_p`.  At a prime of
good reduction this is the usual `a_p = p + 1 - #E(𝔽_p)`; at a prime of bad reduction it is `1`,
`-1` or `0` according to whether the reduction is split multiplicative, nonsplit multiplicative or
additive. -/
noncomputable def aCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + epsilonCoeff W p - (reductionPointCount W p : ℤ)

/-- The inverse of the Euler factor of the Hasse–Weil `L`-function at the prime `p`, namely
`1 - a_p p^{-s} + ε_p p^{1 - 2s}`. -/
noncomputable def eulerFactorInv (W : WeierstrassCurve ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  1 - (aCoeff W p : ℂ) * (p : ℂ) ^ (-s) + (epsilonCoeff W p : ℂ) * (p : ℂ) ^ (1 - 2 * s)

/-- A Weierstrass model `W : WeierstrassCurve ℤ` is a *global minimal model* of an elliptic curve
over `ℚ` if its discriminant is nonzero and has minimal absolute value among all integral models
that become isomorphic to it over `ℚ`. -/
def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 ∧ ∀ W' : WeierstrassCurve ℤ,
    (∃ C : VariableChange ℚ, W'.baseChange ℚ = C • W.baseChange ℚ) → |W.Δ| ≤ |W'.Δ|

/-- `L` is *the* Hasse–Weil `L`-function of the (global minimal) Weierstrass model `W`: it is an
entire function on `ℂ` which, in the region of absolute convergence `Re s > 3/2`, is given by the
Euler product `∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})^{-1}`.

Existence of such an `L` (analytic continuation of the Hasse–Weil `L`-series) is the modularity
theorem; here it is taken as a hypothesis, and `BSD_statement` shows in particular that `L` is
uniquely determined by these properties. -/
structure IsHasseWeilLFunction (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop where
  /-- `W` is a global minimal model (so that the Euler factors below are the correct ones). -/
  minimal : IsGlobalMinimalModel W
  /-- `L` is entire. -/
  entire : ∀ s : ℂ, AnalyticAt ℂ L s
  /-- On `Re s > 3/2`, `L` is given by the Hasse–Weil Euler product. -/
  euler : ∀ s : ℂ, 3 / 2 < s.re → L s = ∏' p : Nat.Primes, (eulerFactorInv W (p : ℕ) s)⁻¹

/-- The *analytic rank* of `W`: the order of vanishing at `s = 1` of its `L`-function. -/
noncomputable def analyticRank (L : ℂ → ℂ) : ℕ∞ := analyticOrderAt L 1

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part) for the elliptic curve given by the
global minimal Weierstrass model `W`, with `L`-function `L`:
`ord_{s=1} L(E, s) = rank E(ℚ)`. -/
def BSD (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop :=
  analyticRank L = (algebraicRank W : ℕ∞)

/-!
## Auxiliary results
-/

/-- At a prime of good reduction, `a_p = p + 1 - #E(𝔽_p)`. -/
theorem aCoeff_of_goodReduction {W : WeierstrassCurve ℤ} {p : ℕ} (hp : HasGoodReduction W p) :
    aCoeff W p = (p : ℤ) + 1 - (reductionPointCount W p : ℤ) := by
  simp [aCoeff, epsilonCoeff, hp]

/-- At a prime of bad reduction, `a_p = p - #E^{ns}(𝔽_p)` and the Euler factor is
`(1 - a_p p^{-s})⁻¹`. -/
theorem eulerFactorInv_of_badReduction {W : WeierstrassCurve ℤ} {p : ℕ}
    (hp : ¬ HasGoodReduction W p) (s : ℂ) :
    aCoeff W p = (p : ℤ) - (reductionPointCount W p : ℤ) ∧
      eulerFactorInv W p s = 1 - (aCoeff W p : ℂ) * (p : ℂ) ^ (-s) := by
  refine ⟨by simp [aCoeff, epsilonCoeff, hp], ?_⟩
  simp [eulerFactorInv, epsilonCoeff, hp]

/-- Rationalizing a torsion abelian group kills it. -/
theorem subsingleton_rat_tensor_of_torsion (M : Type*) [AddCommGroup M]
    (htor : ∀ m : M, ∃ n : ℕ, 0 < n ∧ n • m = 0) :
    Subsingleton (TensorProduct ℤ ℚ M) := by
  have h : ∀ z : TensorProduct ℤ ℚ M, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul q m =>
        obtain ⟨n, hn, hnm'⟩ := htor m
        have hnm : ((n : ℤ)) • m = 0 := by
          rw [Nat.cast_smul_eq_nsmul ℤ]; exact hnm'
        have hcard : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
        have hq : q = ((n : ℤ)) • (q / (n : ℚ)) := by
          rw [zsmul_eq_mul]
          push_cast
          field_simp
        rw [hq, TensorProduct.smul_tmul, hnm, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun x y => by rw [h x, h y]⟩

/-- If the Mordell–Weil group `E(ℚ)` is a torsion group, then the algebraic rank of `E` is `0`. -/
theorem algebraicRank_eq_zero_of_torsion (W : WeierstrassCurve ℤ)
    (htor : ∀ P : MordellWeil W, ∃ n : ℕ, 0 < n ∧ n • P = 0) :
    algebraicRank W = 0 := by
  have : Subsingleton (TensorProduct ℤ ℚ (MordellWeil W)) :=
    subsingleton_rat_tensor_of_torsion _ htor
  exact Module.finrank_zero_of_subsingleton

/-- If the Mordell–Weil group `E(ℚ)` is finite, then the algebraic rank of `E` is `0`. -/
theorem algebraicRank_eq_zero_of_finite (W : WeierstrassCurve ℤ) [Finite (MordellWeil W)] :
    algebraicRank W = 0 :=
  algebraicRank_eq_zero_of_torsion W fun _ => ⟨Nat.card (MordellWeil W), Nat.card_pos,
    card_nsmul_eq_zero'⟩

/-- The Hasse–Weil `L`-function of `W` is unique: any two entire functions agreeing with the Euler
product on `Re s > 3/2` are equal. -/
theorem lFunction_unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsHasseWeilLFunction W L₁) (h₂ : IsHasseWeilLFunction W L₂) : L₁ = L₂ := by
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]
    norm_num
  have hev : L₁ =ᶠ[𝓝 (2 : ℂ)] L₂ :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem)
      (fun s hs => (h₁.euler s hs).trans (h₂.euler s hs).symm)
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => h₁.entire s) (fun s _ => h₂.entire s) hev

/-- Factorization form of the BSD equality: the order of vanishing of `L` at `s = 1` equals the
algebraic rank `r` exactly when `L(s) = (s-1)^r g(s)` near `s = 1` for some analytic `g` with
`g(1) ≠ 0`. -/
theorem bsd_iff_factorization {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hL : IsHasseWeilLFunction W L) :
    BSD W L ↔ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (1 : ℂ), L z = (z - 1) ^ (algebraicRank W) * g z := by
  rw [BSD, analyticRank, (hL.entire 1).analyticOrderAt_eq_natCast]
  constructor
  · rintro ⟨g, hg, hg1, hgL⟩
    exact ⟨g, hg, hg1, hgL.mono fun z hz => by simpa [smul_eq_mul] using hz⟩
  · rintro ⟨g, hg, hg1, hgL⟩
    exact ⟨g, hg, hg1, hgL.mono fun z hz => by simpa [smul_eq_mul] using hz⟩

/-- The rank-zero case of BSD: if the algebraic rank vanishes, BSD is equivalent to the
nonvanishing of `L` at `s = 1`. -/
theorem bsd_iff_L_ne_zero_of_rank_zero {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hL : IsHasseWeilLFunction W L) (hr : algebraicRank W = 0) :
    BSD W L ↔ L 1 ≠ 0 := by
  rw [BSD, analyticRank, hr]
  simpa using (analyticOrderAt_eq_zero (f := L) (z₀ := (1 : ℂ))).trans
    (or_iff_right (not_not_intro (hL.entire 1)))

/-- Base case of BSD: a curve with finite Mordell–Weil group satisfies BSD as soon as its
`L`-function does not vanish at `s = 1`. -/
theorem bsd_of_finite_mordellWeil {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    [Finite (MordellWeil W)] (hL : IsHasseWeilLFunction W L) (h1 : L 1 ≠ 0) :
    BSD W L :=
  (bsd_iff_L_ne_zero_of_rank_zero hL (algebraicRank_eq_zero_of_finite W)).2 h1

/-!
## Main statement
-/

/-- **The Birch and Swinnerton-Dyer statement.**

For an elliptic curve `E/ℚ` given by a global minimal Weierstrass model `W` over `ℤ`, the
Birch–Swinnerton-Dyer conjecture asserts

  `ord_{s=1} L(E, s) = rank E(ℚ)`,

where `L(E, s)` is the entire continuation of the Hasse–Weil `L`-series
`∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})^{-1}` and `rank E(ℚ) = dim_ℚ (ℚ ⊗_ℤ E(ℚ))`.

This theorem records the statement together with the following Lean-checked reductions:

1. the `L`-function of `E` is *unique*, so the conjecture `BSD W L` does not depend on which
   analytic continuation is chosen — in particular `ord_{s=1} L(E,s)` is well defined;
2. `BSD` is equivalent to the local factorization `L(s) = (s-1)^{rank} g(s)` with `g` analytic and
   `g(1) ≠ 0` near `s = 1`;
3. in the rank-zero case BSD reduces to the nonvanishing statement `L(E, 1) ≠ 0`;
4. base case: if the Mordell–Weil group `E(ℚ)` is a torsion group (in particular if it is finite,
   so that the rank is `0`), then `L(E,1) ≠ 0` already implies BSD for `E`. -/
theorem BSD_statement (W : WeierstrassCurve ℤ) (L₁ L₂ : ℂ → ℂ)
    (h₁ : IsHasseWeilLFunction W L₁) (h₂ : IsHasseWeilLFunction W L₂) :
    (L₁ = L₂ ∧ (BSD W L₁ ↔ BSD W L₂)) ∧
    (BSD W L₁ ↔ analyticOrderAt L₁ 1 = (algebraicRank W : ℕ∞)) ∧
    (BSD W L₁ ↔ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
        ∀ᶠ z in 𝓝 (1 : ℂ), L₁ z = (z - 1) ^ (algebraicRank W) * g z) ∧
    (algebraicRank W = 0 → (BSD W L₁ ↔ L₁ 1 ≠ 0)) ∧
    ((∀ P : MordellWeil W, ∃ n : ℕ, 0 < n ∧ n • P = 0) → L₁ 1 ≠ 0 → BSD W L₁) := by
  have huniq : L₁ = L₂ := lFunction_unique h₁ h₂
  exact ⟨⟨huniq, by rw [huniq]⟩, Iff.rfl, bsd_iff_factorization h₁,
    fun hr => bsd_iff_L_ne_zero_of_rank_zero h₁ hr,
    fun htor h1 =>
      (bsd_iff_L_ne_zero_of_rank_zero h₁ (algebraicRank_eq_zero_of_torsion W htor)).2 h1⟩

end Frontier

#print axioms Frontier.BSD_statement

