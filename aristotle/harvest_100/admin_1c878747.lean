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

set_option grind.warning false

namespace Frontier

/-!
## The arithmetic side: the Mordell–Weil rank

We work with an integral Weierstrass model `W : WeierstrassCurve ℤ` with nonzero
discriminant; the associated elliptic curve over `ℚ` is the base change
`W.map (Int.castRingHom ℚ)`, whose group of rational points is
`(W.map (Int.castRingHom ℚ)).toAffine.Point` (affine nonsingular points together with
the point at infinity).
-/

/-- The Mordell–Weil group `E(ℚ)` of the integral Weierstrass model `W`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the `ℚ`-dimension of `ℚ ⊗_ℤ E(ℚ)`
(equivalently, the rank of the free part of the finitely generated abelian group `E(ℚ)`). -/
noncomputable def mwRank (W : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ (MordellWeil W))

/-!
## The analytic side: the Hasse–Weil `L`-function
-/

/-- The number of points of the reduction of `W` modulo `p`: the nonsingular affine points
over `ZMod p` together with the point at infinity. -/
noncomputable def reductionCard (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point

/-- The trace of Frobenius `a_p = p + 1 - #E^ns(𝔽_p)`.
For a minimal model this is the usual `a_p` at good primes, and equals `1`, `-1`, `0`
at primes of split multiplicative, non-split multiplicative and additive reduction
respectively. -/
noncomputable def apCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (reductionCard W p : ℤ)

/-- The local Euler factor at `p`, i.e. the polynomial `1 - a_p p^{-s} + ε_p p^{1-2s}`
where `ε_p = 1` at primes of good reduction and `ε_p = 0` at primes dividing the
(minimal) discriminant. -/
noncomputable def eulerFactor (W : WeierstrassCurve ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  1 - (apCoeff W p : ℂ) * (p : ℂ) ^ (-s) +
    (if (p : ℤ) ∣ W.Δ then 0 else (p : ℂ) ^ (1 - 2 * s))

/-- `L` is *the* Hasse–Weil `L`-function of `W`: it is entire (this is the content of the
modularity theorem) and on the half plane `Re s > 3/2` it is given by the Euler product
`∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})^{-1}`. -/
def IsLFunction (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ L Set.univ ∧
    ∀ s : ℂ, 3 / 2 < s.re → HasProd (fun p : Nat.Primes => (eulerFactor W (p : ℕ) s)⁻¹) (L s)

/-- `W` is a global minimal model: among all integral Weierstrass models isomorphic to `W`
over `ℚ`, it has discriminant of smallest absolute value. (Minimality is what pins down the
Euler factors at the bad primes.) -/
def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ W' : WeierstrassCurve ℤ,
    (∃ C : WeierstrassCurve.VariableChange ℚ,
      W'.map (Int.castRingHom ℚ) = C • W.map (Int.castRingHom ℚ)) →
    W.Δ.natAbs ≤ W'.Δ.natAbs

/-!
## The Birch–Swinnerton-Dyer conjecture (rank part)
-/

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part):
for every elliptic curve `E/ℚ`, given by a global minimal integral Weierstrass model `W`
with nonzero discriminant, the Hasse–Weil `L`-function `L(E, s)` extends to an entire
function and its order of vanishing at `s = 1` equals the rank of the Mordell–Weil group
`E(ℚ)`:
`ord_{s=1} L(E, s) = rank E(ℚ)`. -/
def BSD_statement : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → IsGlobalMinimalModel W →
    ∃ L : ℂ → ℂ, IsLFunction W L ∧ analyticOrderAt L 1 = (mwRank W : ℕ∞)

/-!
## Lean-checked reductions

The conjecture itself is open, and no form of it is available in Mathlib. We record several
unconditional facts which show that the statement above is well posed and reduce it, in low
rank, to concrete analytic assertions.

The Mathlib inputs used below are:
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (the identity theorem, giving uniqueness
of the analytic continuation), `analyticOrderAt` together with `analyticOrderAt_eq_zero` and
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` (the order of vanishing and its
characterisation by derivatives), and `Module.finrank_zero_of_subsingleton`.
-/

/-- The half plane of absolute convergence of the Euler product is open. -/
lemma isOpen_halfPlane : IsOpen {s : ℂ | 3 / 2 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Two `L`-functions of the same curve agree on the half plane `Re s > 3/2`. -/
lemma eqOn_halfPlane_of_isLFunction {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsLFunction W L₁) (h₂ : IsLFunction W L₂) :
    Set.EqOn L₁ L₂ {s : ℂ | 3 / 2 < s.re} := fun _ hs => (h₁.2 _ hs).unique (h₂.2 _ hs)

/-- **Uniqueness of the `L`-function.** Any two entire functions given by the Euler product
of `W` on `Re s > 3/2` are equal: the analytic continuation is unique, so
`ord_{s=1} L(E, s)` is well defined. -/
theorem isLFunction_unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsLFunction W L₁) (h₂ : IsLFunction W L₂) : L₁ = L₂ := by
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  have hev : L₁ =ᶠ[nhds (2 : ℂ)] L₂ :=
    Filter.eventuallyEq_of_mem (isOpen_halfPlane.mem_nhds hmem)
      (eqOn_halfPlane_of_isLFunction h₁ h₂)
  funext z
  exact h₁.1.eqOn_of_preconnected_of_eventuallyEq h₂.1 isPreconnected_univ (Set.mem_univ 2) hev
    (Set.mem_univ z)

/-- Consequently the order of vanishing at `s = 1` does not depend on the choice of the
analytic continuation. -/
theorem analyticOrderAt_eq_of_isLFunction {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsLFunction W L₁) (h₂ : IsLFunction W L₂) :
    analyticOrderAt L₁ 1 = analyticOrderAt L₂ 1 := by
  rw [isLFunction_unique h₁ h₂]

/-- **Reduction to a `∀`-form.** Given that an `L`-function exists, BSD for `W` is
equivalent to the assertion that *every* `L`-function of `W` vanishes to order
`rank E(ℚ)` at `s = 1`. -/
theorem exists_isLFunction_and_order_iff {W : WeierstrassCurve ℤ}
    (hex : ∃ L : ℂ → ℂ, IsLFunction W L) :
    (∃ L : ℂ → ℂ, IsLFunction W L ∧ analyticOrderAt L 1 = (mwRank W : ℕ∞)) ↔
      ∀ L : ℂ → ℂ, IsLFunction W L → analyticOrderAt L 1 = (mwRank W : ℕ∞) := by
  constructor
  · rintro ⟨L₀, hL₀, hord⟩ L hL
    rwa [isLFunction_unique hL hL₀]
  · rintro h
    obtain ⟨L, hL⟩ := hex
    exact ⟨L, hL, h L hL⟩

/-- **Derivative characterisation of the order of vanishing.** For an entire `L`,
`ord_{s=1} L = n` if and only if the first `n` derivatives of `L` vanish at `1` and the
`n`-th one does not. -/
theorem analyticOrderAt_eq_natCast_iff_iteratedDeriv {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 1)
    (n : ℕ) :
    analyticOrderAt L 1 = (n : ℕ∞) ↔
      (∀ i < n, iteratedDeriv i L 1 = 0) ∧ iteratedDeriv n L 1 ≠ 0 := by
  have key := fun m : ℕ =>
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (f := L) (z₀ := 1) (n := m) hL
  constructor
  · intro h
    refine ⟨(key n).mp (le_of_eq h.symm), fun hn => ?_⟩
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt L 1 := by
      refine (key (n + 1)).mpr fun i hi => ?_
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · exact (key n).mp (le_of_eq h.symm) i hi'
      · exact hn
    rw [h] at hle
    have : n + 1 ≤ n := by exact_mod_cast hle
    omega
  · rintro ⟨h1, h2⟩
    have hle : (n : ℕ∞) ≤ analyticOrderAt L 1 := (key n).mpr h1
    have hlt : analyticOrderAt L 1 < ((n + 1 : ℕ) : ℕ∞) :=
      not_le.mp fun hc => h2 ((key (n + 1)).mp hc n (Nat.lt_succ_self n))
    push_cast at hlt
    exact le_antisymm (Order.le_of_lt_add_one hlt) hle

/-- **The rank zero case.** For an entire `L`, BSD in rank `0` says exactly that
`L(E, 1) ≠ 0`. -/
theorem bsd_rank_zero_iff {W : WeierstrassCurve ℤ} {L : ℂ → ℂ} (hL : IsLFunction W L)
    (h0 : mwRank W = 0) :
    analyticOrderAt L 1 = (mwRank W : ℕ∞) ↔ L 1 ≠ 0 := by
  rw [h0, Nat.cast_zero, analyticOrderAt_eq_zero]
  simp [hL.1 1 (Set.mem_univ 1)]

/-- **The rank one case.** For an entire `L`, BSD in rank `1` says exactly that
`L(E, 1) = 0` and `L'(E, 1) ≠ 0`. -/
theorem bsd_rank_one_iff {W : WeierstrassCurve ℤ} {L : ℂ → ℂ} (hL : IsLFunction W L)
    (h1 : mwRank W = 1) :
    analyticOrderAt L 1 = (mwRank W : ℕ∞) ↔ L 1 = 0 ∧ deriv L 1 ≠ 0 := by
  rw [h1, Nat.cast_one, show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) by norm_cast,
    analyticOrderAt_eq_natCast_iff_iteratedDeriv (hL.1 1 (Set.mem_univ 1))]
  constructor
  · rintro ⟨hz, hd⟩
    refine ⟨?_, ?_⟩
    · simpa using hz 0 Nat.one_pos
    · simpa [iteratedDeriv_one] using hd
  · rintro ⟨hz, hd⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · interval_cases i
      simpa using hz
    · simpa [iteratedDeriv_one] using hd

/-- **The torsion case.** If the Mordell–Weil group `E(ℚ)` is a torsion group, its rank
is `0`. -/
theorem mwRank_eq_zero_of_torsion {W : WeierstrassCurve ℤ}
    (h : ∀ P : MordellWeil W, ∃ n : ℕ, n ≠ 0 ∧ n • P = 0) : mwRank W = 0 := by
  have hsub : Subsingleton (TensorProduct ℤ ℚ (MordellWeil W)) := by
    constructor
    suffices hz : ∀ z : TensorProduct ℤ ℚ (MordellWeil W), z = 0 by
      intro x y; rw [hz x, hz y]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul q P =>
        obtain ⟨n, hn, hnP⟩ := h P
        have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        have hq : ((n : ℤ) • (q / n) : ℚ) = q := by
          rw [zsmul_eq_mul]; push_cast; field_simp
        calc (q ⊗ₜ[ℤ] P : TensorProduct ℤ ℚ (MordellWeil W))
            = ((n : ℤ) • (q / n)) ⊗ₜ[ℤ] P := by rw [hq]
          _ = (q / n) ⊗ₜ[ℤ] ((n : ℤ) • P) := TensorProduct.smul_tmul _ _ _
          _ = 0 := by
              rw [show ((n : ℤ) • P) = (n : ℕ) • P by simp, hnP, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact Module.finrank_zero_of_subsingleton

/-- **Base case of BSD.** If `E(ℚ)` is a torsion group, then BSD for `E` is equivalent to
the non-vanishing `L(E, 1) ≠ 0`. -/
theorem bsd_iff_of_torsion {W : WeierstrassCurve ℤ} {L : ℂ → ℂ} (hL : IsLFunction W L)
    (h : ∀ P : MordellWeil W, ∃ n : ℕ, n ≠ 0 ∧ n • P = 0) :
    analyticOrderAt L 1 = (mwRank W : ℕ∞) ↔ L 1 ≠ 0 :=
  bsd_rank_zero_iff hL (mwRank_eq_zero_of_torsion h)

end Frontier

