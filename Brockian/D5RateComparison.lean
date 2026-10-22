import Brockian.D5EquivariantOperators
import Brockian.D5MarkovContraction

/-!
# From D₅ Fourier phases to real heat-semigroup contraction

The explicit five-by-five matrix below is the real coordinate matrix of
`D5RateOperators.realRateAction`. Nonnegative rates give a symmetric balanced
Markov Laplacian. The two Fourier cross-product conditions from
`rateOperator_commute_iff_two` therefore imply contraction under addition of
a nonnegative rate increment, for every real finite ℓᵖ norm with `1 ≤ p`
and for the supremum norm.

The comparison holds for every initial vector and after subtraction of any
constant. In particular it holds for distance to the uniform vector `1/5`.
The phase conditions are sufficient for this conclusion; this file does
not assert they are necessary for norm monotonicity.
-/

open BigOperators Matrix
open scoped Matrix.Norms.Operator
open Brockian.D5RateOperators Brockian.MarkovContraction

namespace Brockian.D5RateComparison

noncomputable section

local notation "conjC" => (starRingEnd ℂ)

/-- The real coordinate matrix of the seven-rate D₅ vertex Laplacian. -/
def realRateMatrix (a : SymmetricRates) : Matrix (Fin 5) (Fin 5) ℝ :=
  let x := a.rotationOne
  let y := a.rotationTwo
  let b := a.reflection
  let B := ∑ k, b k
  !![2*x + 2*y + B - b 0, -x - b 4, -y - b 3, -y - b 2, -x - b 1;
     -x - b 4, 2*x + 2*y + B - b 3, -x - b 2, -y - b 1, -y - b 0;
     -y - b 3, -x - b 2, 2*x + 2*y + B - b 1, -x - b 0, -y - b 4;
     -y - b 2, -y - b 1, -x - b 0, 2*x + 2*y + B - b 4, -x - b 3;
     -x - b 1, -y - b 0, -y - b 4, -x - b 3, 2*x + 2*y + B - b 2]

/-- This explicit matrix acts as the already-defined real D₅ rate operator. -/
theorem realRateMatrix_mulVec (a : SymmetricRates) (f : Fin 5 → ℝ) :
    realRateMatrix a *ᵥ f = realRateAction a f := by
  have hn1 : -(1 : Fin 5) = 4 := by decide
  have hn2 : -(2 : Fin 5) = 3 := by decide
  have hn3 : -(3 : Fin 5) = 2 := by decide
  have hn4 : -(4 : Fin 5) = 1 := by decide
  funext x
  fin_cases x <;>
    simp [realRateMatrix, realRateAction, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, hn1, hn2, hn3, hn4] <;> ring

theorem realRateMatrix_transpose (a : SymmetricRates) :
    (realRateMatrix a)ᵀ = realRateMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem realRateMatrix_row_zero (a : SymmetricRates) :
    realRateMatrix a *ᵥ (1 : Fin 5 → ℝ) = 0 := by
  rw [realRateMatrix_mulVec]
  funext x
  norm_num [realRateAction]

theorem realRateMatrix_col_zero (a : SymmetricRates) :
    (1 : Fin 5 → ℝ) ᵥ* realRateMatrix a = 0 := by
  rw [← Matrix.mulVec_transpose, realRateMatrix_transpose]
  exact realRateMatrix_row_zero a

/-- Inversion-symmetric nonnegative rates give a balanced Markov Laplacian. -/
theorem realRateMatrix_balanced (a : SymmetricRates) (ha : a.Nonnegative) :
    BalancedLaplacian (realRateMatrix a) := by
  refine ⟨?_, realRateMatrix_row_zero a, realRateMatrix_col_zero a⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [realRateMatrix]
  all_goals
    linarith [ha.1, ha.2.1, ha.2.2 0, ha.2.2 1, ha.2.2 2,
      ha.2.2 3, ha.2.2 4]

theorem realRateMatrix_add (a b : SymmetricRates) :
    realRateMatrix (addRates a b) = realRateMatrix a + realRateMatrix b := by
  apply Matrix.ext_iff_mulVec.mpr
  intro f
  rw [Matrix.add_mulVec, realRateMatrix_mulVec, realRateMatrix_mulVec,
    realRateMatrix_mulVec]
  funext x
  simp only [realRateAction, addRates, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

/-- Complex Fourier commutation transfers to the actual real coordinate matrices. -/
theorem realRateMatrix_commute_of_rateOperator_commute (a b : SymmetricRates)
    (h : Commute (rateOperator a) (rateOperator b)) :
    Commute (realRateMatrix a) (realRateMatrix b) := by
  change realRateMatrix a * realRateMatrix b = realRateMatrix b * realRateMatrix a
  apply Matrix.ext_iff_mulVec.mpr
  intro f
  simp only [← Matrix.mulVec_mulVec, realRateMatrix_mulVec]
  exact realRateAction_commute_of_rateOperator_commute a b h f

/-- The exact two nontrivial Fourier-block tests provide real matrix commutation. -/
theorem realRateMatrix_commute_of_two_phases (a b : SymmetricRates)
    (hphase :
      (reflectionSymbol a.reflection 1 * conjC (reflectionSymbol b.reflection 1)).im = 0 ∧
      (reflectionSymbol a.reflection 2 * conjC (reflectionSymbol b.reflection 2)).im = 0) :
    Commute (realRateMatrix a) (realRateMatrix b) := by
  exact realRateMatrix_commute_of_rateOperator_commute a b
    ((rateOperator_commute_iff_two a b).mpr hphase)

/-- The real five-vertex heat matrix associated with the D₅ rates. -/
def rateHeat (a : SymmetricRates) (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  heat (realRateMatrix a) t

/-- The exact factorization that supplies the additional Markov averaging step. -/
theorem rateHeat_add_of_two_phases (a b : SymmetricRates)
    (hphase :
      (reflectionSymbol a.reflection 1 * conjC (reflectionSymbol b.reflection 1)).im = 0 ∧
      (reflectionSymbol a.reflection 2 * conjC (reflectionSymbol b.reflection 2)).im = 0)
    (t : ℝ) : rateHeat (addRates a b) t = rateHeat b t * rateHeat a t := by
  simp only [rateHeat, realRateMatrix_add]
  exact heat_add_of_commute (realRateMatrix a) (realRateMatrix b)
    (realRateMatrix_commute_of_two_phases a b hphase) t

theorem rateHeat_doublyStochastic (a : SymmetricRates) (ha : a.Nonnegative)
    {t : ℝ} (ht : 0 ≤ t) : rateHeat a t ∈ doublyStochastic ℝ (Fin 5) :=
  heat_doublyStochastic (realRateMatrix a) (realRateMatrix_balanced a ha) ht

/-- A phase-compatible nonnegative D₅ increment contracts each finite ℓᵖ distance
to a constant. No positivity assumption on the starting vector is needed. -/
theorem phase_increment_lpNorm_sub_const_le (a b : SymmetricRates)
    (hb : b.Nonnegative)
    (hphase :
      (reflectionSymbol a.reflection 1 * conjC (reflectionSymbol b.reflection 1)).im = 0 ∧
      (reflectionSymbol a.reflection 2 * conjC (reflectionSymbol b.reflection 2)).im = 0)
    (v : Fin 5 → ℝ) (c : ℝ) {t p : ℝ} (ht : 0 ≤ t) (hp : 1 ≤ p) :
    lpNorm p (rateHeat (addRates a b) t *ᵥ v - fun _ => c) ≤
      lpNorm p (rateHeat a t *ᵥ v - fun _ => c) := by
  simp only [rateHeat, realRateMatrix_add]
  exact commuting_increment_lpNorm_sub_const_le (realRateMatrix a) (realRateMatrix b)
    (realRateMatrix_balanced b hb) (realRateMatrix_commute_of_two_phases a b hphase)
    v c ht hp

theorem phase_increment_supNorm_sub_const_le (a b : SymmetricRates)
    (hb : b.Nonnegative)
    (hphase :
      (reflectionSymbol a.reflection 1 * conjC (reflectionSymbol b.reflection 1)).im = 0 ∧
      (reflectionSymbol a.reflection 2 * conjC (reflectionSymbol b.reflection 2)).im = 0)
    (v : Fin 5 → ℝ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖rateHeat (addRates a b) t *ᵥ v - (fun _ => c)‖ ≤
      ‖rateHeat a t *ᵥ v - (fun _ => c)‖ := by
  simp only [rateHeat, realRateMatrix_add]
  exact commuting_increment_supNorm_sub_const_le (realRateMatrix a) (realRateMatrix b)
    (realRateMatrix_balanced b hb) (realRateMatrix_commute_of_two_phases a b hphase)
    v c ht

/-- For nonnegative base rates and increment, both evolutions are Markov heat
matrices and all ℓᵖ distances (`1 ≤ p ≤ ∞`) to uniform equilibrium do not increase. -/
theorem markov_rate_comparison (a b : SymmetricRates)
    (ha : a.Nonnegative) (hb : b.Nonnegative)
    (hphase :
      (reflectionSymbol a.reflection 1 * conjC (reflectionSymbol b.reflection 1)).im = 0 ∧
      (reflectionSymbol a.reflection 2 * conjC (reflectionSymbol b.reflection 2)).im = 0)
    (v : Fin 5 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    rateHeat a t ∈ doublyStochastic ℝ (Fin 5) ∧
    rateHeat (addRates a b) t ∈ doublyStochastic ℝ (Fin 5) ∧
    (∀ p : ℝ, 1 ≤ p →
      lpNorm p (rateHeat (addRates a b) t *ᵥ v - fun _ => (1 / 5 : ℝ)) ≤
        lpNorm p (rateHeat a t *ᵥ v - fun _ => (1 / 5 : ℝ))) ∧
    ‖rateHeat (addRates a b) t *ᵥ v - (fun _ => (1 / 5 : ℝ))‖ ≤
      ‖rateHeat a t *ᵥ v - (fun _ => (1 / 5 : ℝ))‖ := by
  refine ⟨rateHeat_doublyStochastic a ha ht,
    rateHeat_doublyStochastic (addRates a b) (addRates_nonnegative ha hb) ht, ?_, ?_⟩
  · intro p hp
    exact phase_increment_lpNorm_sub_const_le a b hb hphase v (1 / 5) ht hp
  · exact phase_increment_supNorm_sub_const_le a b hb hphase v (1 / 5) ht

end

end Brockian.D5RateComparison
