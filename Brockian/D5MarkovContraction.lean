import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Commuting finite Markov generators contract every finite ℓᵖ norm

The analytic part of the D₅ rate comparison is independent of the group.
We first prove contraction for doubly stochastic matrices, including the
supremum norm, then show that the exponential of a balanced Markov
generator is doubly stochastic. Commuting generator increments therefore
give norm monotonicity for every starting vector, including distance to a
constant equilibrium.

The phase criterion in `D5EquivariantOperators` supplies the separate
algebraic commutation hypothesis. Commutation is a sufficient condition
for these inequalities; no converse about norm monotonicity is asserted.
-/

open BigOperators Matrix
open scoped Matrix.Norms.Operator

namespace Brockian.MarkovContraction

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The usual unnormalised finite ℓᵖ norm, used below only for `1 ≤ p`. -/
def lpNorm (p : ℝ) (v : n → ℝ) : ℝ :=
  (∑ i, |v i| ^ p) ^ (1 / p)

theorem abs_mulVec_le (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (v : n → ℝ) (i : n) :
    |(P *ᵥ v) i| ≤ ∑ j, P i j * |v j| := by
  calc
    |(P *ᵥ v) i| = |∑ j, P i j * v j| := rfl
    _ ≤ ∑ j, |P i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, P i j * |v j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (hP.1 i j)]

theorem sum_rpow_mulVec_le (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (v : n → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i, |(P *ᵥ v) i| ^ p ≤ ∑ i, |v i| ^ p := by
  calc
    ∑ i, |(P *ᵥ v) i| ^ p ≤ ∑ i, ∑ j, P i j * |v j| ^ p := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |(P *ᵥ v) i| ^ p ≤ (∑ j, P i j * |v j|) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) (abs_mulVec_le P hP v i) (by linarith)
        _ ≤ ∑ j, P i j * |v j| ^ p :=
          Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (P i) (fun j => |v j|)
            (fun j _ => hP.1 i j) (sum_row_of_mem_doublyStochastic hP i)
            (fun j _ => abs_nonneg _) hp
    _ = ∑ j, |v j| ^ p := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hP j, one_mul]

theorem lpNorm_mulVec_le (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (v : n → ℝ) {p : ℝ} (hp : 1 ≤ p) : lpNorm p (P *ᵥ v) ≤ lpNorm p v := by
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  · exact sum_rpow_mulVec_le P hP v hp
  · exact div_nonneg zero_le_one (by linarith)

/-- On functions on a finite type, this is precisely the ℓ∞ norm. -/
theorem supNorm_mulVec_le (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (v : n → ℝ) : ‖P *ᵥ v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
  intro i
  rw [Real.norm_eq_abs]
  calc
    |(P *ᵥ v) i| ≤ ∑ j, P i j * |v j| := abs_mulVec_le P hP v i
    _ ≤ ∑ j, P i j * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j)
        (hP.1 i j)
    _ = ‖v‖ := by rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP i, one_mul]

theorem mulVec_const (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) (c : ℝ) :
    P *ᵥ (fun _ => c) = fun _ => c := by
  funext i
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP i, one_mul]

theorem lpNorm_sub_const_mulVec_le (P : Matrix n n ℝ)
    (hP : P ∈ doublyStochastic ℝ n) (v : n → ℝ) (c : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    lpNorm p (P *ᵥ v - fun _ => c) ≤ lpNorm p (v - fun _ => c) := by
  have heq : P *ᵥ (v - (fun _ : n => c)) = P *ᵥ v - (fun _ : n => c) := by
    rw [Matrix.mulVec_sub P v (fun _ : n => c), mulVec_const P hP c]
  rw [← heq]
  exact lpNorm_mulVec_le P hP (v - (fun _ : n => c)) hp

theorem supNorm_sub_const_mulVec_le (P : Matrix n n ℝ)
    (hP : P ∈ doublyStochastic ℝ n) (v : n → ℝ) (c : ℝ) :
    ‖P *ᵥ v - (fun _ => c)‖ ≤ ‖v - (fun _ => c)‖ := by
  have heq : P *ᵥ (v - (fun _ : n => c)) = P *ᵥ v - (fun _ : n => c) := by
    rw [Matrix.mulVec_sub P v (fun _ : n => c), mulVec_const P hP c]
  rw [← heq]
  exact supNorm_mulVec_le P hP (v - (fun _ : n => c))

private theorem pow_entry_nonneg (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∀ k i j, 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hA l j))

theorem exp_entry_nonneg (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j) (i j : n) :
    0 ≤ NormedSpace.exp A i j := by
  have hs := Pi.hasSum.mp (Pi.hasSum.mp
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j
  exact le_of_le_of_eq
    (tsum_nonneg (fun k => mul_nonneg (by positivity) (pow_entry_nonneg A hA k i j)))
    hs.tsum_eq

private theorem exp_scalar (c : ℝ) :
    NormedSpace.exp (c • (1 : Matrix n n ℝ)) = Real.exp c • (1 : Matrix n n ℝ) := by
  have h : c • (1 : Matrix n n ℝ) = Matrix.diagonal (fun _ => c) := by
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  rw [h, Matrix.exp_diagonal]
  ext i j
  simp [Pi.coe_exp, ← Real.exp_eq_exp_ℝ, Matrix.diagonal_apply, Matrix.one_apply]

/-- Nonnegative off-diagonal entries suffice for entrywise positivity of the exponential. -/
theorem exp_entry_nonneg_of_offdiag (A : Matrix n n ℝ)
    (hA : ∀ i j, i ≠ j → 0 ≤ A i j) (i j : n) : 0 ≤ NormedSpace.exp A i j := by
  let c : ℝ := ∑ k, |A k k|
  let B := A + c • (1 : Matrix n n ℝ)
  have hB : ∀ i j, 0 ≤ B i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hi : |A i i| ≤ c := by
        exact Finset.single_le_sum (fun k _ => abs_nonneg (A k k)) (Finset.mem_univ i)
      have hai := neg_abs_le (A i i)
      simp only [B, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      linarith
    · simpa [B, Matrix.one_apply, hij] using hA i j hij
  have hsplit : A = (-c) • (1 : Matrix n n ℝ) + B := by
    dsimp [B]
    module
  rw [hsplit, Matrix.exp_add_of_commute _ _ ((Commute.one_left B).smul_left (-c)), exp_scalar,
    Matrix.smul_mul, one_mul]
  exact mul_nonneg (Real.exp_nonneg _) (exp_entry_nonneg B hB i j)

theorem exp_mulVec_of_mulVec_eq_zero (A : Matrix n n ℝ) (v : n → ℝ)
    (hA : A *ᵥ v = 0) : NormedSpace.exp A *ᵥ v = v := by
  let F : Matrix n n ℝ →ₗ[ℝ] (n → ℝ) := (Matrix.mulVecBilin ℝ ℝ).flip v
  have hF : Continuous F := F.continuous_of_finiteDimensional
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map F.toAddMonoidHom hF
  have hpow (k : ℕ) : (A ^ (k + 1)) *ᵥ v = 0 := by
    rw [pow_succ, ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  have hseries : (fun k : ℕ => F ((k.factorial : ℝ)⁻¹ • A ^ k)) =
      fun k : ℕ => if k = 0 then v else 0 := by
    funext k
    cases k with
    | zero => simp [F]
    | succ k => simp [F, hpow]
  change HasSum (fun k : ℕ => F ((k.factorial : ℝ)⁻¹ • A ^ k)) (NormedSpace.exp A *ᵥ v) at hs
  rw [hseries] at hs
  simpa using hs.unique (hasSum_ite_eq 0 v)

/-- A positive Laplacian for a finite Markov chain with uniform stationary measure. -/
structure BalancedLaplacian (L : Matrix n n ℝ) : Prop where
  offdiag : ∀ i j, i ≠ j → L i j ≤ 0
  row_zero : L *ᵥ 1 = 0
  col_zero : 1 ᵥ* L = 0

def heat (L : Matrix n n ℝ) (t : ℝ) : Matrix n n ℝ := NormedSpace.exp ((-t) • L)

theorem heat_doublyStochastic (L : Matrix n n ℝ) (hL : BalancedLaplacian L)
    {t : ℝ} (ht : 0 ≤ t) : heat L t ∈ doublyStochastic ℝ n := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply exp_entry_nonneg_of_offdiag
    intro i j hij
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ht) (hL.offdiag i j hij)
  · apply exp_mulVec_of_mulVec_eq_zero
    rw [Matrix.smul_mulVec, hL.row_zero, smul_zero]
  · have htL : ((-t) • L)ᵀ *ᵥ (1 : n → ℝ) = 0 := by
      simp only [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_transpose,
        hL.col_zero, smul_zero]
    simpa only [heat, Matrix.exp_transpose, Matrix.mulVec_transpose] using
      exp_mulVec_of_mulVec_eq_zero (((-t) • L)ᵀ) (1 : n → ℝ) htL

theorem heat_add_of_commute (L K : Matrix n n ℝ) (hLK : Commute L K) (t : ℝ) :
    heat (L + K) t = heat K t * heat L t := by
  unfold heat
  rw [add_comm L K, smul_add]
  exact Matrix.exp_add_of_commute _ _ ((hLK.symm.smul_left (-t)).smul_right (-t))

/-- A commuting nonnegative generator increment contracts every real finite ℓᵖ norm. -/
theorem commuting_increment_lpNorm_le (L K : Matrix n n ℝ)
    (hK : BalancedLaplacian K) (hLK : Commute L K) (v : n → ℝ)
    {t p : ℝ} (ht : 0 ≤ t) (hp : 1 ≤ p) :
    lpNorm p (heat (L + K) t *ᵥ v) ≤ lpNorm p (heat L t *ᵥ v) := by
  rw [heat_add_of_commute L K hLK t, ← Matrix.mulVec_mulVec]
  exact lpNorm_mulVec_le (heat K t) (heat_doublyStochastic K hK ht) _ hp

theorem commuting_increment_supNorm_le (L K : Matrix n n ℝ)
    (hK : BalancedLaplacian K) (hLK : Commute L K) (v : n → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heat (L + K) t *ᵥ v‖ ≤ ‖heat L t *ᵥ v‖ := by
  rw [heat_add_of_commute L K hLK t, ← Matrix.mulVec_mulVec]
  exact supNorm_mulVec_le (heat K t) (heat_doublyStochastic K hK ht) _

/-- Centering at any constant reference vector preserves the comparison.
For a nonempty state space and a balanced base Laplacian, taking
`c = 1 / Fintype.card n` gives distance to the uniform equilibrium. -/
theorem commuting_increment_lpNorm_sub_const_le (L K : Matrix n n ℝ)
    (hK : BalancedLaplacian K) (hLK : Commute L K) (v : n → ℝ) (c : ℝ)
    {t p : ℝ} (ht : 0 ≤ t) (hp : 1 ≤ p) :
    lpNorm p (heat (L + K) t *ᵥ v - fun _ => c) ≤
      lpNorm p (heat L t *ᵥ v - fun _ => c) := by
  rw [heat_add_of_commute L K hLK t, ← Matrix.mulVec_mulVec]
  exact lpNorm_sub_const_mulVec_le (heat K t) (heat_doublyStochastic K hK ht) _ c hp

theorem commuting_increment_supNorm_sub_const_le (L K : Matrix n n ℝ)
    (hK : BalancedLaplacian K) (hLK : Commute L K) (v : n → ℝ) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heat (L + K) t *ᵥ v - (fun _ => c)‖ ≤ ‖heat L t *ᵥ v - (fun _ => c)‖ := by
  rw [heat_add_of_commute L K hLK t, ← Matrix.mulVec_mulVec]
  exact supNorm_sub_const_mulVec_le (heat K t) (heat_doublyStochastic K hK ht) _ c

end
end Brockian.MarkovContraction
