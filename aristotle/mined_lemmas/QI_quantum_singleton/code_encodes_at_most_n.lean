/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix Module ComplexConjugate
open scoped ComplexOrder

/-! ## Part I : linear algebra over `ℂ`

The mathematical core of the quantum Singleton bound is a statement about the ranks of the
various flattenings of a four-index complex tensor.  This part develops the required
rank inequalities.
-/

/-- Every column of a complex matrix can be expanded in a family of `X.rank` vectors, with
coefficients that are (fixed) linear functionals applied to the column. -/

theorem code_encodes_at_most_n {q n k d : ℕ} (hq : 2 ≤ q) (Q : QECC q n k d) : k ≤ n := by
  have h := code_dim_le (by omega) Q ∅ ∅ (by simp) (detects_empty _) (detects_empty _)
  simp only [Finset.union_self, Finset.compl_empty, Finset.card_univ, Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right hq).mp h

/-- **The quantum Singleton bound.**

An `[[n, k, d]]_q` quantum code with `q ≥ 2` and `k ≥ 1` satisfies `n - k ≥ 2 (d - 1)`. -/
