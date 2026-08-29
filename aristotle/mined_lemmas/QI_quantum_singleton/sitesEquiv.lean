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

def sitesEquiv {n q : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    Str n q ≃
      (({i // i ∈ A} → Fin q) × ({i // i ∈ B} → Fin q) × ({i // i ∈ (A ∪ B)ᶜ} → Fin q)) where
  toFun s := (fun i => s i, fun i => s i, fun i => s i)
  invFun t := asm A B t.1 t.2.1 t.2.2
  left_inv s := by
    funext j
    simp only [asm]
    by_cases h : j ∈ A
    · simp [h]
    · by_cases h' : j ∈ B <;> simp [h, h']
  right_inv t := by
    obtain ⟨a, b, c⟩ := t
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; simp [asm, i.2]
    · funext i
      have hnA : (i : Fin n) ∉ A := fun hc => (Finset.disjoint_left.mp hAB hc) i.2
      simp [asm, hnA, i.2]
    · funext i
      have hi := i.2
      simp only [Finset.mem_compl, Finset.mem_union, not_or] at hi
      simp [asm, hi.1, hi.2]

