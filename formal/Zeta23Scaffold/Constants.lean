/-
  Zeta23Scaffold/Constants.lean — DRAFT statement scaffold (T2, uncharted-RH-machinery program).

  SOURCE: "More than two thirds of the zeta zeros on the critical line" (CLAUDE, 10 Aug 2026),
  ~/Desktop/zeta-two-thirds.pdf — §1.3 (eq. 1.3, the window constants), §7.5(d)-(f)
  (Christoffel function of the sine-kernel moment sequence, the 13/18 conditional rung),
  §7.5(g) (the cubic weight ψ under RH).

  REGISTER INTENT: every `theorem` in this file is a PROVED-target — finite, exact
  rational/real algebra, no analysis, no zeta. These are the "assembly identities" the
  preprint's conditional ladder rests on, isolated as one-shot Aristotle targets.
  All bodies are `sorry` BY DESIGN: T2 drafts, the fleet proves.

  TOOLCHAIN: our AXLE pin, leanprover/lean4:v4.32.0 + matching Mathlib.
  (The zeta-23-lean reference repo pins v4.33.0-rc2; nothing here uses post-4.32 API.)

  HONESTY MAP (which targets are trivial algebra vs real content):
  * H_one / Hd_one / F_one / two_F_one_sub_one       — TRIVIAL (norm_num-grade).
  * Hd_ge_F_iff / H_nonneg_iff_threshold             — one-variable real algebra with √6;
                                                       MEDIUM (field_simp + nlinarith / sqrt API).
  * hankelAtOne_det / christoffelLambda2_eq / ladder — 3×3 rational determinant + arithmetic;
                                                       MEDIUM (Matrix.det_fin_three + norm_num).
  * psi_le_one / psi_eq_one_of_small                 — integer-cubic inequality; the key is the
                                                       verified factorization
                                                       18·(1 − ψ(m)) = (m−2)(m−3)(m+3)  (m ≥ 2).
  * NOTHING in this file asserts anything about ζ, the sine process, or the matrix G̃.
    The connection of these constants to zero-counting is scaffolded in Ladder.lean and is
    CONDITIONAL/CONJECTURE material there, never here.

  FIRST-UNJUSTIFIED-STEP NOTES (modeling choices made in this file):
  * `christoffelLambda2` is DEFINED as the Hankel-determinant ratio
    det M₃ / det (minor₀₀ M₃) for the moment matrix M₃ = (m_{i+j})_{0≤i,j≤2}. By Cramer this
    equals 1/(e₀ᵀ M₃⁻¹ e₀), the classical Christoffel function Λ₂(0) of the moment sequence —
    the paper's Λ₂(0;1) (§7.5(d),(f)). We take the determinant ratio as the DEFINITION so the
    target is pure rational arithmetic; the equivalence with the variational definition
    (min ∫p² over p(0)=1, deg ≤ 2) is NOT stated here and is not needed for the ladder algebra.
  * The moment values m_k(1) = 1, 4/3, 2, 13/4 (k = 1..4) are TRANSCRIBED from §7.5(f) as
    rational constants. Their analytic content (moments of the limiting spectral distribution
    of the sine-kernel Gram matrix over the sine process) is Hypotheses.lean material; here
    they are just numbers feeding the Hankel matrix. m_0 = 1 is the normalization.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section

namespace Zeta23Scaffold

/-! ## 1. The window constants of §1.3, eq. (1.3)

Paper, verbatim: "For 0 < λ ≤ 1 put
  H(λ) := 2 − 1/λ − λ/3,   H_d(λ) := (1 + H(λ))/2,   F(λ) := λ/(1 + λ²/3);
  H(1) = 2/3, H_d(1) = 5/6, F(1) = 3/4;
  H_d(λ) ≥ F(λ) ⟺ H(λ) ≥ 0 ⟺ λ ≥ 3 − √6 = 0.5505…". -/

/-- H(λ) := 2 − 1/λ − λ/3  [eq. (1.3)]. The 2/3 of Theorems A and B is H(1).
    (§1.4 assembly: s ≥ 4N − 2N − (1/λ + λ/3)N = (H(λ) − o(1))N.) -/
def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- H_d(λ) := (1 + H(λ))/2  [eq. (1.3)]. The 5/6 of Theorem C is H_d(1). -/
def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- F(λ) := λ/(1 + λ²/3)  [eq. (1.3)]. The Cauchy–Schwarz branch; F(1) = 3/4. -/
def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- PROVED-target (EASY): H(1) = 2/3  [eq. (1.3)]. -/
theorem Hwin_one : Hwin 1 = 2 / 3 := by
  sorry

/-- PROVED-target (EASY): H_d(1) = 5/6  [eq. (1.3)]. -/
theorem Hd_one : Hd 1 = 5 / 6 := by
  sorry

/-- PROVED-target (EASY): F(1) = 3/4  [eq. (1.3)]. -/
theorem Fwin_one : Fwin 1 = 3 / 4 := by
  sorry

/-- PROVED-target (EASY): 2F(1) − 1 = 1/2 — the simple-zero constant of the Cauchy–Schwarz
    route (§1.4, §7.5(c): "The Cauchy–Schwarz route … stops at 2F(1) − 1 = 1/2 for simple
    zeros"). -/
theorem two_Fwin_one_sub_one : 2 * Fwin 1 - 1 = 1 / 2 := by
  sorry

/-- PROVED-target (MEDIUM): on 0 < λ ≤ 1, H_d(λ) ≥ F(λ) ⟺ H(λ) ≥ 0  [eq. (1.3), third line].
    Route: H_d − F = (1+H)/2 − λ/(1+λ²/3); clear denominators (both positive) and compare;
    both sides reduce to the sign of 6λ − 3 − λ² over 3λ(3 + λ²) > 0. -/
theorem Hd_ge_Fwin_iff {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  sorry

/-- PROVED-target (MEDIUM): on 0 < λ ≤ 1, H(λ) ≥ 0 ⟺ λ ≥ 3 − √6  [eq. (1.3), third line].
    Route: 0 ≤ 2 − 1/λ − λ/3 ⟺ (multiply by 3λ > 0) λ² − 6λ + 3 ≤ 0; the roots are 3 ± √6
    and λ ≤ 1 < 3 + √6, so the condition is 3 − √6 ≤ λ. Needs `Real.sq_sqrt` (6 ≥ 0) and
    `Real.sqrt_lt'`-style comparisons; nlinarith with (Real.sqrt 6)^2 = 6 as an auxiliary
    hypothesis should close both directions. -/
theorem Hwin_nonneg_iff_threshold {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  sorry

/-! ## 2. The sine-kernel moment values at λ = 1 and the Christoffel value Λ₂(0;1)  [§7.5(d),(f)]

Paper §7.5(f), verbatim: "One computes m_k(1) = 1, 4/3, 2, 13/4 for k ≤ 4, so Λ₂(0;1) = 5/36".
Paper §7.5(d): "if the normalised moments d⁻¹ tr(G̃/ℓ₁)^k, k ≤ 2m, are known, the sharp lower
bound for n₊^θ(G̃)/d is 1 − Λ_m(0), Λ_m the Christoffel function of the moment sequence at 0."

Here the m_k(1) are rational CONSTANTS (transcription; analytic meaning lives in
Hypotheses.lean). Λ₂(0) is defined by the Hankel-determinant ratio (see header note). -/

/-- The moment sequence m_0, …, m_4 at λ = 1: (1, 1, 4/3, 2, 13/4)  [§7.5(f)].
    m_0 = 1 is the normalization (empirical spectral distribution is a probability measure). -/
def momentAtOne : Fin 5 → ℚ := ![1, 1, 4/3, 2, 13/4]

/-- The 3×3 Hankel (moment) matrix M₃ = (m_{i+j}(1))_{0≤i,j≤2}. -/
def hankelAtOne : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3;
     1, 4/3, 2;
     4/3, 2, 13/4]

/-- PROVED-target (MEDIUM): det M₃ = 5/108. Route: `Matrix.det_fin_three` + `norm_num`
    (or `decide`-free pure rational arithmetic; keep it kernel-light). -/
theorem hankelAtOne_det : hankelAtOne.det = 5 / 108 := by
  sorry

/-- Λ₂(0;1), DEFINED as the Hankel ratio det M₃ / det(minor₀₀ M₃)
    (= 1/(e₀ᵀ M₃⁻¹ e₀) by Cramer; see header modeling note). minor₀₀ = [[4/3, 2], [2, 13/4]]. -/
def christoffelLambda2 : ℚ := hankelAtOne.det / (Matrix.det !![(4:ℚ)/3, 2; 2, 13/4])

/-- PROVED-target (MEDIUM): Λ₂(0;1) = 5/36  [§7.5(f), verbatim: "so Λ₂(0;1) = 5/36"].
    (det minor₀₀ = 13/3 − 4 = 1/3; (5/108)/(1/3) = 5/36. Verified rationally off-line.) -/
theorem christoffelLambda2_eq : christoffelLambda2 = 5 / 36 := by
  sorry

/-- PROVED-target (EASY, given the previous): the Chebyshev–Markov–Stieltjes count
    1 − Λ₂(0;1) = 31/36 — the §7.5(d) sharp lower bound for n₊^θ(G̃)/d under known moments
    k ≤ 4. -/
theorem one_sub_christoffel : 1 - christoffelLambda2 = 31 / 36 := by
  sorry

/-- PROVED-target (EASY, given the previous): the 13/18 ladder assembly:
    2·(1 − Λ₂(0;1)) − 1 = 13/18. This is the pure-arithmetic shadow of "HL*(4,λ) for all
    λ < 1 would give lim inf N₀ˢ(T,2T)/N(T,2T) ≥ 13/18 via the count of Proposition 4.5"
    [§7.5(f)] — the simple-zero count s₁ ≥ 2n₊ − N applied at n₊/d → 31/36, d/N → 1
    (λ → 1⁻). The ANALYTIC content of that sentence is NOT here (see Ladder.lean);
    this theorem is only the constant-assembly 2·31/36 − 1 = 26/36 = 13/18. -/
theorem ladder_thirteen_eighteenths : 2 * (1 - christoffelLambda2) - 1 = 13 / 18 := by
  sorry

/-! ## 3. The cubic weight of §7.5(g) (distinct zeros under RH)

Paper §7.5(g), verbatim: "the certificate of Proposition 4.4(iii) can be run with cubic
weights ψ(m) = ½m + (1/18)(2m² − m³) + (4/9)·1_{m=1}: one checks ψ(m) ≤ 1 for all integers
m ≥ 1 (equality at m = 1, 2, 3)". This check is finite algebra and is stated here as a
PROVED-target; everything else in §7.5(g) (RH, tr G̃³, Schur–Horn, the window
v(s) = cos(8s/5), the constant 0.85082…) is NOT formalized in this file. -/

/-- ψ(m) = ½m + (1/18)(2m² − m³) + (4/9)·1_{m=1}  [§7.5(g)], as a rational function of a
    natural number (values cast to ℚ). -/
def psiCubic (m : ℕ) : ℚ :=
  (m : ℚ) / 2 + (2 * (m : ℚ) ^ 2 - (m : ℚ) ^ 3) / 18 + if m = 1 then 4 / 9 else 0

/-- PROVED-target (MEDIUM): ψ(m) ≤ 1 for all integers m ≥ 1  [§7.5(g), "one checks
    ψ(m) ≤ 1 for all integers m ≥ 1"]. Route: for m = 1 compute ψ(1) = 1; for m ≥ 2 use the
    exact factorization  18·(1 − ψ(m)) = (m − 2)(m − 3)(m + 3)  (identity over ℚ after the
    indicator vanishes; verified off-line for m = 2..7), which is ≥ 0 for integer m ≥ 2 since
    (m−2)(m−3) ≥ 0 (consecutive-ish integers: both ≤ 0 factors only at no integer, cases
    m = 2, 3, m ≥ 4) and m + 3 > 0. `rcases` on m ≤ 3 then nlinarith/positivity. -/
theorem psiCubic_le_one : ∀ m : ℕ, 1 ≤ m → psiCubic m ≤ 1 := by
  sorry

/-- PROVED-target (EASY): equality holds at m = 1, 2, 3  [§7.5(g), "(equality at
    m = 1, 2, 3)"]. -/
theorem psiCubic_eq_one_of_small : psiCubic 1 = 1 ∧ psiCubic 2 = 1 ∧ psiCubic 3 = 1 := by
  sorry

end Zeta23Scaffold
