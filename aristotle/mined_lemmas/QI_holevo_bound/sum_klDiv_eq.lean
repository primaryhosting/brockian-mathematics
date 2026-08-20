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

theorem sum_klDiv_eq {X ι : Type*} [Fintype X] [Fintype ι] (p : X → ℝ) (r : X → ι → ℝ) :
    ∑ x, p x * klDiv (r x) (fun i => ∑ x', p x' * r x' i)
      = shannonEntropy (fun i => ∑ x', p x' * r x' i) - ∑ x, p x * shannonEntropy (r x) := by
  have step : ∀ x, p x * klDiv (r x) (fun i => ∑ x', p x' * r x' i) + p x * shannonEntropy (r x)
      = ∑ i, -(p x * r x i * Real.log (∑ x', p x' * r x' i)) := by
    intro x
    simp only [klDiv, shannonEntropy, Real.negMulLog, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : ∑ x, (p x * klDiv (r x) (fun i => ∑ x', p x' * r x' i) + p x * shannonEntropy (r x))
      = shannonEntropy (fun i => ∑ x', p x' * r x' i) := by
    simp only [step]
    rw [Finset.sum_comm]
    simp only [shannonEntropy, Real.negMulLog]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_add_distrib] at key
  linarith

/-- Classical data-processing inequality for mutual information. -/
