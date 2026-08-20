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

theorem classical_holevo {X ι κ : Type*} [Fintype X] [Fintype ι] [Fintype κ]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (r : X → ι → ℝ) (hr0 : ∀ x i, 0 ≤ r x i)
    (T : ι → κ → ℝ) (hT0 : ∀ i k, 0 ≤ T i k) (hT1 : ∀ i, ∑ k, T i k = 1) :
    shannonEntropy (fun k => ∑ x, p x * ∑ i, r x i * T i k)
        - ∑ x, p x * shannonEntropy (fun k => ∑ i, r x i * T i k)
      ≤ shannonEntropy (fun i => ∑ x, p x * r x i) - ∑ x, p x * shannonEntropy (r x) := by
  have hqb : ∀ k, (∑ x, p x * ∑ i, r x i * T i k) = ∑ i, (∑ x, p x * r x i) * T i k := by
    intro k
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
  have hL := sum_klDiv_eq p (fun x k => ∑ i, r x i * T i k)
  have hR := sum_klDiv_eq p r
  rw [← hL, ← hR]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases (hp0 x).eq_or_lt with hpx | hpx
  · simp [← hpx]
  · refine mul_le_mul_of_nonneg_left ?_ (hp0 x)
    have hac : ∀ i, (∑ x', p x' * r x' i) = 0 → r x i = 0 := by
      intro i hi
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x' _ => mul_nonneg (hp0 x') (hr0 x' i))).1 hi x (mem_univ x)
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (ne_of_gt hpx)
      · exact h
    have hdpi := klDiv_stochastic_le T hT0 hT1 (r x) (fun i => ∑ x', p x' * r x' i)
      (hr0 x) (fun i => Finset.sum_nonneg fun x' _ => mul_nonneg (hp0 x') (hr0 x' i)) hac
    simpa only [hqb] using hdpi

/-! ## Quantum setting -/

open Matrix Polynomial
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A density matrix: positive semidefinite with unit trace. -/
