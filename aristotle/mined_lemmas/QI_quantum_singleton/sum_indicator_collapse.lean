/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

lemma sum_indicator_collapse {A' P : Type*} [Fintype A'] [DecidableEq A'] [Fintype P]
    [DecidableEq P] (f g : A' → P → ℂ) (u u' : A') :
    ∑ X : A' × P, ∑ Y : A' × P,
      f X.1 X.2 * ((if X.1 = u then (1:ℂ) else 0) * (if Y.1 = u' then 1 else 0) *
        (if X.2 = Y.2 then 1 else 0)) * g Y.1 Y.2 = ∑ p : P, f u p * g u' p := by
  simp [Fintype.sum_prod_type, Finset.sum_ite_eq', mul_comm]

/-- `E` is an error operator supported on the coordinate set `T`: outside `T` it acts as the
identity (it is of the form `F ⊗ 1`, with `F` acting on the coordinates in `T`). -/
