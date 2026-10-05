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

def Detects {n q : ℕ} (Code : Submodule ℂ (HSpace n q)) (S : Finset (Fin n)) : Prop :=
  ∃ sig : Str n q → Str n q → ℂ, ∀ x ∈ Code, ∀ y ∈ Code, ∀ u v : Str n q,
    corr S x y u v = inner ℂ x y * sig u v

/-- An `[[n, k, d]]_q` quantum error correcting code: a subspace of the `n`-qudit Hilbert space
of dimension `q ^ k` all of whose errors of weight `< d` are detected. -/
structure QECC (q n k d : ℕ) where
  /-- the code subspace -/
  space : Submodule ℂ (HSpace n q)
  /-- the code encodes `k` qudits -/
  dim : Module.finrank ℂ space = q ^ k
  /-- every error of weight at most `d - 1` is detected -/
  detects : ∀ S : Finset (Fin n), S.card < d → Detects space S

/-- Assembling a string out of its restrictions to `A`, to `B` and to the complement of
`A ∪ B`. -/
