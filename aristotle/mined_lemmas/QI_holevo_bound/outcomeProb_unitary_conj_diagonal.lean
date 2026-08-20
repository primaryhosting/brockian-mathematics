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

theorem outcomeProb_unitary_conj_diagonal (U : Matrix n n ℂ) (v : n → ℝ) (F : Matrix n n ℂ) :
    outcomeProb (U * diagonal (fun i => (v i : ℂ)) * Uᴴ) F
      = ∑ i, v i * ((Uᴴ * F * U) i i).re := by
  have h1 : (U * diagonal (fun i => (v i : ℂ)) * Uᴴ * F).trace
      = (diagonal (fun i => (v i : ℂ)) * (Uᴴ * F * U)).trace := by
    rw [show U * diagonal (fun i => (v i : ℂ)) * Uᴴ * F
        = U * (diagonal (fun i => (v i : ℂ)) * (Uᴴ * F)) from by noncomm_ring,
      Matrix.trace_mul_comm, mul_assoc]
  rw [outcomeProb, h1]
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum, Complex.mul_re]

/-- Averaging commutes with unitary conjugation of diagonal matrices. -/
