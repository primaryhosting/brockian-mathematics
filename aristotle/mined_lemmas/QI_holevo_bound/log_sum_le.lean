/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `QI.log_sum_le`, `QI.klDiv_stochastic_le`, `QI.classical_holevo`: the classical core, namely the
  log-sum inequality, the data-processing inequality for the Kullback–Leibler divergence, and the
  resulting data-processing inequality for mutual information.
* `QI.vonNeumannEntropy`, `QI.IsState`, `QI.IsPOVM`, `QI.outcomeProb`, `QI.holevoChi`,
  `QI.measuredInfo`, `QI.accessibleInfo`: the quantum-information definitions.
* `QI.holevo_bound`: for an ensemble of density matrices measured by an arbitrary POVM, the
  mutual information between the ensemble label and the measurement outcome is at most the
  Holevo quantity `χ`.
* `QI.accessibleInfo_le_holevoChi`: the same statement for the supremum over POVMs.

## Scope

The ensemble is assumed to consist of *commuting* density matrices: they are given as
`ρ x = U * diagonal (r x) * Uᴴ` for one fixed unitary `U` and probability vectors `r x`.  The
measurement, on the other hand, is a completely arbitrary POVM, so the argument is not a purely
classical one: the POVM has to be turned into a stochastic matrix via `i ↦ (Uᴴ (E y) U) i i`.
The fully general (non-commuting) Holevo bound needs monotonicity of the *quantum* relative
entropy under measurement, which is not available in Mathlib.
-/

open Finset

namespace QI

/-! ## Classical information-theoretic core -/

/-- Shannon entropy of a finite (sub)probability vector, with the convention `0 * log 0 = 0`. -/

theorem log_sum_le {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hac : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * (Real.log (∑ i, a i) - Real.log (∑ i, b i)) ≤ klDiv a b := by
  have hB0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  rcases hB0.eq_or_lt with hBz | hBpos
  · have hbz : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hb j)).1 hBz.symm i (mem_univ i)
    have haz : ∀ i, a i = 0 := fun i => hac i (hbz i)
    simp [klDiv, haz, hbz]
  · have hbpos : ∀ i, 0 < a i → 0 < b i := by
      intro i hai
      rcases (hb i).eq_or_lt with h | h
      · exact absurd (hac i h.symm) (ne_of_gt hai)
      · exact h
    have key : ∀ i ∈ (univ : Finset ι),
        a i - b i * ((∑ j, a j) / (∑ j, b j))
          ≤ a i * (Real.log (a i) - Real.log (b i))
            - a i * (Real.log (∑ j, a j) - Real.log (∑ j, b j)) := by
      intro i _
      rcases (ha i).eq_or_lt with hai | hai
      · have : 0 ≤ b i * ((∑ j, a j) / (∑ j, b j)) :=
          mul_nonneg (hb i) (div_nonneg (Finset.sum_nonneg fun j _ => ha j) hB0)
        simp only [← hai]
        linarith
      · have hApos : 0 < ∑ j, a j :=
          lt_of_lt_of_le hai (Finset.single_le_sum (fun j _ => ha j) (mem_univ i))
        have hbi := hbpos i hai
        have ht : 0 < (b i * (∑ j, a j)) / (a i * (∑ j, b j)) := by positivity
        have hlog := Real.log_le_sub_one_of_pos ht
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (ne_of_gt hbi) (ne_of_gt hApos),
          Real.log_mul (ne_of_gt hai) (ne_of_gt hBpos)] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hai)
        have hsimp : a i * ((b i * (∑ j, a j)) / (a i * (∑ j, b j)) - 1)
            = b i * ((∑ j, a j) / (∑ j, b j)) - a i := by
          field_simp
        rw [hsimp] at hmul
        nlinarith [hmul]
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
    have hzero : (∑ j, b j) * ((∑ j, a j) / (∑ j, b j)) = ∑ j, a j := by
      field_simp
    rw [hzero] at hsum
    simpa [klDiv] using hsum

/-- Data-processing inequality for the KL divergence under a stochastic map. -/
