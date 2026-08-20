import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma bornProb_commutingState (E U : Matrix n n ℂ) (r : n → ℝ) :
    bornProb E (commutingState U r) = bornProb (Uᴴ * E * U) (diagState r) := by
  rw [bornProb, bornProb, commutingState, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- **Holevo bound.** Let `{p i, ρ i}` be an ensemble of pairwise commuting density matrices,
i.e. states `ρ i = U * diag (r i) * Uᴴ` diagonal in one common orthonormal basis (the columns of
the unitary `U`), with spectra `r i`. For an arbitrary POVM `{E y}`, the mutual information
between the label `i` and the measurement outcome `y` — and hence the accessible information,
which is its maximum over all measurements — is at most the Holevo quantity
`χ = S(∑ p i ρ i) - ∑ p i S(ρ i)`.

The normalisation hypotheses `hp1` and `hr1` (which say that `p` is a probability vector and
each `ρ i` has unit trace) are part of the definition of a quantum ensemble; they are recorded
here for faithfulness even though the inequality itself does not need them. -/
