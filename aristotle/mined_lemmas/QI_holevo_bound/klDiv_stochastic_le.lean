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

theorem klDiv_stochastic_le {ι κ : Type*} [Fintype ι] [Fintype κ] (T : ι → κ → ℝ)
    (hT0 : ∀ i k, 0 ≤ T i k) (hT1 : ∀ i, ∑ k, T i k = 1)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hac : ∀ i, b i = 0 → a i = 0) :
    klDiv (fun k => ∑ i, a i * T i k) (fun k => ∑ i, b i * T i k) ≤ klDiv a b := by
  have hterm : ∀ i k, (a i * T i k) * (Real.log (a i * T i k) - Real.log (b i * T i k))
      = T i k * (a i * (Real.log (a i) - Real.log (b i))) := by
    intro i k
    rcases (hT0 i k).eq_or_lt with hTk | hTk
    · simp [← hTk]
    rcases (ha i).eq_or_lt with hai | hai
    · simp [← hai]
    · have hbi : 0 < b i := by
        rcases (hb i).eq_or_lt with h | h
        · exact absurd (hac i h.symm) (ne_of_gt hai)
        · exact h
      rw [Real.log_mul (ne_of_gt hai) (ne_of_gt hTk), Real.log_mul (ne_of_gt hbi) (ne_of_gt hTk)]
      ring
  have h1 : klDiv a b = ∑ k, klDiv (fun i => a i * T i k) (fun i => b i * T i k) := by
    simp only [klDiv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hterm i]
    rw [← Finset.sum_mul, hT1 i, one_mul]
  rw [h1, klDiv]
  refine Finset.sum_le_sum fun k _ => ?_
  refine log_sum_le (fun i => a i * T i k) (fun i => b i * T i k)
    (fun i => mul_nonneg (ha i) (hT0 i k)) (fun i => mul_nonneg (hb i) (hT0 i k)) ?_
  intro i hi
  dsimp only at hi ⊢
  rcases mul_eq_zero.1 hi with h | h
  · rw [hac i h]; ring
  · rw [h]; ring

/-- The mutual information of a classical ensemble, written with KL divergences. -/
