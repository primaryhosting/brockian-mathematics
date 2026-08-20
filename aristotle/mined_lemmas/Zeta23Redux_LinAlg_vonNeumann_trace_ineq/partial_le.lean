/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Zeta23Redux.LinAlg

/-- Abel summation / Hardy–Littlewood–Pólya: if `m` is decreasing on `range d` and the partial
sums of `f` are dominated by those of `g`, with equal total sums, then `∑ m f ≤ ∑ m g`. -/

lemma partial_le (d k : ℕ) (hk : k ≤ d) (c n : ℕ → ℝ)
    (hc0 : ∀ j, j < d → 0 ≤ c j) (hc1 : ∀ j, j < d → c j ≤ 1)
    (hsum : ∑ j ∈ range d, c j = (k : ℝ))
    (hn : ∀ i j, i ≤ j → j < d → n j ≤ n i) :
    ∑ j ∈ range d, c j * n j ≤ ∑ j ∈ range k, n j := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simp only [Nat.cast_zero] at hsum
    have hz : ∀ j ∈ range d, c j * n j = 0 := by
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      have hcj : c j = 0 := by
        by_contra hne
        have hpos : 0 < c j := lt_of_le_of_ne (hc0 j hjd) (Ne.symm hne)
        have : 0 < ∑ j ∈ range d, c j :=
          Finset.sum_pos' (fun i hi => hc0 i (Finset.mem_range.mp hi)) ⟨j, hj, hpos⟩
        linarith
      simp [hcj]
    rw [Finset.sum_congr rfl hz]
    simp
  · set p := k - 1 with hp
    have hpd : p < d := by omega
    set chi : ℕ → ℝ := fun j => if j < k then 1 else 0 with hchi
    have hfil : (range d).filter (fun j => j < k) = range k := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
    have hsum2 : ∑ j ∈ range d, chi j * n j = ∑ j ∈ range k, n j := by
      simp only [hchi, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfil]
    have hsum3 : ∑ j ∈ range d, (c j - chi j) = 0 := by
      rw [Finset.sum_sub_distrib, hsum]
      have hck : ∑ j ∈ range d, chi j = (k : ℝ) := by
        simp only [hchi]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfil]
        simp
      rw [hck]; ring
    have key : ∑ j ∈ range d, (c j - chi j) * (n j - n p) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      by_cases hjk : j < k
      · have h1 : c j - chi j ≤ 0 := by simp only [hchi, if_pos hjk]; linarith [hc1 j hjd]
        have h2 : 0 ≤ n j - n p := by linarith [hn j p (by omega) hpd]
        nlinarith
      · have h1 : 0 ≤ c j - chi j := by simp only [hchi, if_neg hjk]; linarith [hc0 j hjd]
        have h2 : n j - n p ≤ 0 := by linarith [hn p j (by omega) hjd]
        nlinarith
    have expand : ∑ j ∈ range d, (c j - chi j) * (n j - n p)
        = (∑ j ∈ range d, c j * n j - ∑ j ∈ range d, chi j * n j)
          - n p * ∑ j ∈ range d, (c j - chi j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum3, hsum2, mul_zero, sub_zero] at expand
    linarith [key, expand.le, expand.symm.le]

/-- The doubly stochastic bilinear bound: for a doubly stochastic matrix `S` and decreasing
sequences `m`, `n` we have `∑_{i,j} m i * n j * S i j ≤ ∑_i m i * n i`. -/
