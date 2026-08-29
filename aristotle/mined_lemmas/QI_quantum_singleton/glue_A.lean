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

lemma glue_A {n q : ℕ} (A B : Finset (Fin n)) (u : Str n q)
    (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
    (c : {i // i ∈ (A ∪ B)ᶜ} → Fin q) :
    glue A u (asm A B a b c) = asm A B (fun i => u i) b c := by
  funext j
  simp only [glue, asm]
  by_cases h : j ∈ A <;> simp [h]

