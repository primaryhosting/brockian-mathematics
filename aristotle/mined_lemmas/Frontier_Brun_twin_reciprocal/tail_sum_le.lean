import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma tail_sum_le (I : ℕ) :
    ∑ i ∈ range I, (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0) ≤ ∑' j, vv j := by
  classical
  set g : ℕ → ℝ := fun i => if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0 with hg
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i
    rw [hg]
    dsimp only
    split
    · positivity
    · exact le_rfl
  have hgle : ∀ i, g i ≤ 4 * Real.exp (-(jj i : ℝ)) := by
    intro i
    rw [hg]
    dsimp only
    split
    · exact le_rfl
    · positivity
  set J := I + 16 with hJ
  have hIJ : I ≤ aa J := le_trans (by omega) (le_aa J)
  have h16J : 16 ≤ J := by omega
  have hzero : ∑ i ∈ range (aa 16), g i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hg]
    dsimp only
    rw [if_neg]
    exact Nat.not_le.2 (Finset.mem_range.1 hi)
  have hinner : ∀ j ∈ Ico 16 J, ∑ i ∈ Ico (aa j) (aa (j+1)), g i ≤ vv j := by
    intro j hj
    have hj16 : 16 ≤ j := (Finset.mem_Ico.1 hj).1
    have hpt : ∀ i ∈ Ico (aa j) (aa (j+1)), g i ≤ 4 * Real.exp (-(j:ℝ)) := by
      intro i hi
      have hij : aa j ≤ i := (Finset.mem_Ico.1 hi).1
      have hjji : j ≤ jj i := le_jj hj16 hij
      have : Real.exp (-(jj i : ℝ)) ≤ Real.exp (-(j:ℝ)) := by
        apply Real.exp_le_exp.2
        have : (j:ℝ) ≤ (jj i : ℝ) := by exact_mod_cast hjji
        linarith
      have := hgle i
      linarith
    calc ∑ i ∈ Ico (aa j) (aa (j+1)), g i
        ≤ ∑ _i ∈ Ico (aa j) (aa (j+1)), 4 * Real.exp (-(j:ℝ)) := Finset.sum_le_sum hpt
      _ = ((aa (j+1) - aa j : ℕ) : ℝ) * (4 * Real.exp (-(j:ℝ))) := by
          rw [Finset.sum_const, Nat.card_Ico]
          simp [nsmul_eq_mul]
      _ ≤ (aa (j+1) : ℝ) * (4 * Real.exp (-(j:ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.sub_le _ _
      _ = 4 * (aa (j+1) : ℝ) * Real.exp (-(j:ℝ)) := by ring
      _ ≤ vv j := aa_succ_le j
  calc ∑ i ∈ range I, g i
      ≤ ∑ i ∈ range (aa J), g i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hIJ)
        · intro i _ _
          exact hgnn i
    _ = ∑ i ∈ range (aa 16), g i + ∑ i ∈ Ico (aa 16) (aa J), g i :=
        (Finset.sum_range_add_sum_Ico g (aa_mono h16J)).symm
    _ = ∑ i ∈ Ico (aa 16) (aa J), g i := by rw [hzero, zero_add]
    _ = ∑ j ∈ Ico 16 J, ∑ i ∈ Ico (aa j) (aa (j+1)), g i := sum_Ico_partition g h16J
    _ ≤ ∑ j ∈ Ico 16 J, vv j := Finset.sum_le_sum hinner
    _ ≤ ∑ j ∈ range J, vv j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          exact Finset.mem_range.2 (Finset.mem_Ico.1 hx).2
        · intro i _ _
          exact vv_nonneg i
    _ ≤ ∑' j, vv j := Summable.sum_le_tsum _ (fun i _ => vv_nonneg i) summable_vv

/-- Every partial sum of the block sums is bounded. -/
