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

theorem holevoChi_nonneg {X : Type*} [Fintype X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → n → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, ρ x = U * diagonal (fun i => (r x i : ℂ)) * Uᴴ) :
    0 ≤ holevoChi p ρ := by
  have hvn : ∀ x, vonNeumannEntropy (ρ x) = shannonEntropy (r x) := by
    intro x; rw [hρ x, vonNeumannEntropy_unitary_conj_diagonal hU1]
  have havg : vonNeumannEntropy (∑ x, (p x : ℂ) • ρ x)
      = shannonEntropy (fun i => ∑ x, p x * r x i) := by
    simp only [hρ]
    rw [sum_smul_unitary_conj_diagonal, vonNeumannEntropy_unitary_conj_diagonal hU1]
  have hrb0 : ∀ i, 0 ≤ ∑ x, p x * r x i :=
    fun i => Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hr0 x i)
  have hrb1 : ∑ i, (∑ x, p x * r x i) = 1 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hr1, mul_one]
    exact hp1
  rw [holevoChi, havg]
  simp only [hvn]
  rw [← sum_klDiv_eq p r]
  refine Finset.sum_nonneg fun x _ => ?_
  rcases (hp0 x).eq_or_lt with hpx | hpx
  · simp [← hpx]
  refine mul_nonneg (hp0 x) ?_
  have hac : ∀ i, (∑ x', p x' * r x' i) = 0 → r x i = 0 := by
    intro i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x' _ => mul_nonneg (hp0 x') (hr0 x' i))).1 hi x (mem_univ x)
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (ne_of_gt hpx)
    · exact h
  have hls := log_sum_le (r x) (fun i => ∑ x', p x' * r x' i) (hr0 x) hrb0 hac
  rwa [hr1 x, hrb1, Real.log_one, sub_self, mul_zero] at hls

/-- The accessible information of an ensemble, i.e. the supremum over all POVMs with outcome
set `Y` of the mutual information between the ensemble label and the measurement outcome. -/
