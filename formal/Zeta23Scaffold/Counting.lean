/-
  Zeta23Scaffold/Counting.lean — DRAFT statement scaffold (T2, uncharted-RH-machinery program).

  SOURCE: preprint §1.3 [The results] — the six counting functions, stated directly against
  Mathlib's `riemannZeta`. IDIOMS: this file deliberately mirrors zeta-23-lean
  (github.com/anthropics/zeta-23-lean, Apache-2.0), Zeta23/Statement.lean §1
  (IsNontrivialZero as ζ(ρ) = 0 ∧ 0 < Re ρ < 1; multiplicity via `analyticOrderAt … |>.toNat`;
  counts as finsum-of-multiplicity resp. `Set.ncard` over zero sets), RE-STATED independently
  at OUR toolchain — we do not import or port their proofs.

  REGISTER INTENT: the `def`s are definitions (no register); the two lemmas at the bottom are
  PROVED-targets (set-inclusion monotonicity, no analysis). Nothing here claims any zero-count
  bound.

  TOOLCHAIN: lean-4.32.0 + matching Mathlib.
  API RISK NOTES (4.32 vs the reference repo's 4.33.0-rc2):
  * `analyticOrderAt` (Mathlib.Analysis.Analytic.Order) — the ℕ∞-valued order; present in
    Mathlib from early 2025 (successor of `AnalyticAt.order`). If absent at our pin, fall back
    to `(hf : AnalyticAt ℂ riemannZeta ρ).order`; the def below assumes the standalone
    function form.
  * `Set.ncard`, `finsum` (∑ᶠ) — stable API, low risk.
  * `riemannZeta` (Mathlib.NumberTheory.LSeries.RiemannZeta) — stable.

  FIRST-UNJUSTIFIED-STEP NOTES (modeling choices):
  * "Nontrivial zero" is rendered as STRIP zero (0 < Re ρ < 1), exactly as in the paper's §1.3
    and zeta-23-lean; Mathlib's `RiemannHypothesis` phrases nontriviality differently
    (not −2(n+1), ≠ 1) — every strip zero is nontrivial in that sense, and the converse is
    classical but NOT needed for statements.
  * Windows are positive-ordinate: T₁ < Im ρ ≤ T₂ (NOT |γ|), matching the paper.
  * Multiplicity via `analyticOrderAt riemannZeta ρ |>.toNat`: ⊤ ↦ 0, so `1 ≤ zeroMult ρ`
    silently encodes "ζ not locally ≡ 0 at ρ" — a seam fact (true, classical), not assumed
    here. Counts with multiplicity use ∑ᶠ, which is 0 on infinite supports; finiteness of
    each window is again a classical seam fact not assumed in the defs.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Order
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Complex Set

noncomputable section

namespace Zeta23Scaffold

/-- ρ is a nontrivial zero of ζ: ζ(ρ) = 0 with 0 < Re ρ < 1  [§1.3, "Write ρ = β + iγ for a
    nontrivial zero of ζ(s)"]. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ, the multiplicity of ρ  [§1.3], as the analytic order of vanishing of ζ at ρ. -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The window {ρ nontrivial : T₁ < γ ≤ T₂}, γ = Im ρ  [§1.3]. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} counted with multiplicity  [§1.3]. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N_d(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂}, each distinct point counted once  [§1.3]. -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N₀(T₁,T₂) := on-line zeros counted with multiplicity  [§1.3]. -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ

/-- N₀*(T₁,T₂) := on-line zeros counted without multiplicity  [§1.3]. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- N₀ˢ(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂, β = 1/2, m_ρ = 1} — simple on-line zeros  [§1.3].
    This is the count the 13/18 conditional rung bounds  [§7.5(f)]. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-- Nˢ(T₁,T₂) := the number of simple zeros in the window  [§1.3]. -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

/-! ## PROVED-targets: unconditional ncard monotonicity links (no analysis, no seam facts)

Fragments of the paper's trivial chain (1.1) that need NO finiteness/multiplicity seam:
inclusions of the underlying sets plus `Set.ncard_le_ncard` — except that `ncard` of an
INFINITE set is 0, so the inclusion direction alone gives ≤ only under a finiteness
hypothesis. We therefore state them with an explicit finiteness hypothesis on the larger
set, which is the honest unconditional form. (The full chain (1.1) including the
∑ᶠ-multiplicity counts needs the ZetaSeam facts and is NOT drafted here.) -/

/-- PROVED-target (EASY): N₀ˢ ≤ N₀* on every window, given the window is finite
    (fragment of [eq. (1.1)]). Route: `Set.ncard_le_ncard` with inter_subset. -/
theorem N0simple_le_N0star (T₁ T₂ : ℝ) (hfin : (zerosIn T₁ T₂).Finite) :
    N0simple T₁ T₂ ≤ N0star T₁ T₂ := by
  sorry

/-- PROVED-target (EASY): N₀ˢ ≤ Nˢ and N₀* ≤ N_d on every finite window
    (fragments of [eq. (1.1)]). -/
theorem N0simple_le_Nsimple_and_N0star_le_Ndist (T₁ T₂ : ℝ)
    (hfin : (zerosIn T₁ T₂).Finite) :
    N0simple T₁ T₂ ≤ Nsimple T₁ T₂ ∧ N0star T₁ T₂ ≤ Ndist T₁ T₂ := by
  sorry

/-! ## Statement-layer Props for the conditional ladder (referenced by Ladder.lean)

These mirror zeta-23-lean's `ThmA_statement` pattern: dyadic ε-forms, each a `Prop` DEF
(no claim of proof anywhere). -/

/-- The 13/18 rung, dyadic ε-form  [§7.5(f)]: "HL*(4,λ) for all λ < 1 would give
    lim inf N₀ˢ(T,2T)/N(T,2T) ≥ 13/18". CONDITIONAL-register statement; defined here,
    conditionally derived in Ladder.lean, proved by NOBODY in this scaffold. -/
def Rung1318_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (13 / 18 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)

/-- Proportion one of simple on-line zeros, dyadic ε-form  [§7.5(f)]: "HL*(k₀,λ) for all k₀
    and all λ < 1 would give proportion 1 (of simple zeros on the line), the ceiling of
    Proposition 7.4". CONDITIONAL-register statement. -/
def SimpleProportionOne_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)

/-- Distinct zeros under RH, WEAKENED-constant dyadic ε-form  [§7.5(g)]: the paper certifies
    lim inf N_d/N ≥ 0.85082… under RH (cubic weight ψ, window v(s) = cos(8s/5), Schur–Horn,
    N_s ≥ (19/27 − o(1))N on RH). MODELING CHOICE: the paper's constant is not closed-form
    (it involves interval-certified m₂, m₃ for that window); we state the rung with the
    WEAKER rational constant 17/20 = 0.85 < 0.85082…, which the paper's argument dominates.
    CONJECTURE-register statement (conditional on RH; the derivation is unformalized). -/
def DistinctUnderRH_statement : Prop :=
  RiemannHypothesis →
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (17 / 20 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T)

end Zeta23Scaffold
