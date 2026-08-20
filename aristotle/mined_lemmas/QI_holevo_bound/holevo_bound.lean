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

theorem holevo_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → n → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, ρ x = U * diagonal (fun i => (r x i : ℂ)) * Uᴴ)
    (E : Y → Matrix n n ℂ) (hE : IsPOVM E) :
    measuredInfo p ρ E ≤ holevoChi p ρ := by
  have hop : ∀ x y, outcomeProb (ρ x) (E y) = ∑ i, r x i * ((Uᴴ * E y * U) i i).re := by
    intro x y; rw [hρ x, outcomeProb_unitary_conj_diagonal]
  have hvn : ∀ x, vonNeumannEntropy (ρ x) = shannonEntropy (r x) := by
    intro x; rw [hρ x, vonNeumannEntropy_unitary_conj_diagonal hU1]
  have havg : vonNeumannEntropy (∑ x, (p x : ℂ) • ρ x)
      = shannonEntropy (fun i => ∑ x, p x * r x i) := by
    simp only [hρ]
    rw [sum_smul_unitary_conj_diagonal, vonNeumannEntropy_unitary_conj_diagonal hU1]
  rw [measuredInfo, holevoChi, havg]
  simp only [hop, hvn]
  exact classical_holevo p hp0 r hr0 (fun i y => ((Uᴴ * E y * U) i i).re)
    (fun i y => povm_stochastic_nonneg U hE i y) (povm_stochastic_sum hU1 hE)

/-- The Holevo quantity of an ensemble is nonnegative. -/
