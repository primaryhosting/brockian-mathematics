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

theorem povm_stochastic_sum {Y : Type*} [Fintype Y] {U : Matrix n n ℂ} (hU1 : Uᴴ * U = 1)
    {E : Y → Matrix n n ℂ} (hE : IsPOVM E) (i : n) :
    ∑ y, ((Uᴴ * E y * U) i i).re = 1 := by
  have hsum : ∑ y, (Uᴴ * E y * U) i i = (1 : Matrix n n ℂ) i i := by
    have : ∑ y, Uᴴ * E y * U = (1 : Matrix n n ℂ) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE.2, mul_one, hU1]
    calc ∑ y, (Uᴴ * E y * U) i i = (∑ y, Uᴴ * E y * U) i i := (Matrix.sum_apply i i _ _).symm
      _ = (1 : Matrix n n ℂ) i i := by rw [this]
  rw [← Complex.re_sum, hsum]
  simp

/-- **The Holevo bound.**

Let `{p x, ρ x}` be an ensemble of density matrices on a finite-dimensional Hilbert space that
are simultaneously diagonalized by a unitary `U`, with spectra `r x`, and let `E` be an
arbitrary POVM.  Then the classical mutual information between the ensemble label and the
measurement outcome is at most the Holevo quantity
`χ = S(∑ x p x ρ x) - ∑ x p x S(ρ x)`.  Since this holds for every POVM `E`, the accessible
information (the supremum over POVMs) is at most `χ`.

The normalization hypotheses `hp1` and `hr1` say that `p` is a probability distribution and each
`ρ x` is a genuine density matrix (see `QI.isState_unitary_conj_diagonal`); they are recorded for
faithfulness even though the inequality itself does not need them. -/
