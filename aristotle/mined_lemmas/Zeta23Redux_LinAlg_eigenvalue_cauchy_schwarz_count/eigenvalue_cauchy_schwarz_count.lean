import Mathlib

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

import Mathlib

/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**

For eigenvalues `ev : Fin d → ℝ` and a threshold `θ ≥ 0`, let `s` be the set of indices whose
eigenvalue exceeds `θ` and `n = #s`.  If `θ * d < ∑ ev`, then
`(∑ ev - θ * d)^2 ≤ n * ∑ (ev i)^2`.

The proof: eigenvalues below the threshold only decrease `∑ i, (ev i - θ)`, so the excess
`∑ ev - θ * d` is at most `∑_{i ∈ s} ev i`; then Cauchy–Schwarz on the `n` eigenvalues above `θ`. -/

theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * d < ∑ i, ev i) :
    ((∑ i, ev i) - theta * d) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  subst hs hn
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hsdef
  -- Step 1: the excess is at most the sum of the eigenvalues above the threshold.
  have hsplit : ∑ i, (ev i - theta) =
      (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i),
        (ev i - theta) := by
    rw [hsdef]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have hneg : ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i), (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_filter, not_lt] at hi
    linarith [hi.2]
  have hexcess : (∑ i, ev i) - theta * d ≤ ∑ i ∈ s, ev i := by
    have h1 : ∑ i, (ev i - theta) = (∑ i, ev i) - theta * d := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_univ, mul_comm]
    have h2 : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
      apply Finset.sum_le_sum
      intro i _
      linarith
    linarith [hsplit ▸ h1]
  -- Step 2: square, then Cauchy–Schwarz on `s`.
  have hpos : (0:ℝ) ≤ (∑ i, ev i) - theta * d := by linarith
  have hsq : ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 :=
    pow_le_pow_left₀ hpos hexcess 2
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmono : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    positivity
  have hcard : (0:ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  nlinarith [hsq, hcs, mul_le_mul_of_nonneg_left hmono hcard]

/-- Sanity check: the hypotheses of `eigenvalue_cauchy_schwarz_count` are satisfiable,
so the theorem is not vacuous. -/
example : ((∑ _i : Fin 2, (1:ℝ)) - 0 * (2:ℕ)) ^ 2 ≤ ((2:ℕ) : ℝ) * ∑ _i : Fin 2, (1:ℝ) ^ 2 :=
  eigenvalue_cauchy_schwarz_count 2 (fun _ => 1) 0 le_rfl
    (Finset.univ.filter (fun i => (0:ℝ) < (fun _ : Fin 2 => (1:ℝ)) i)) rfl 2 (by simp)
    (by norm_num)

end Zeta23Redux.LinAlg

