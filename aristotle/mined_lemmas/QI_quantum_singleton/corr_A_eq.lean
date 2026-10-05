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

lemma corr_A_eq {n q : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B) (x y : HSpace n q)
    (u v : Str n q) :
    corr A x y u v = (q ^ A.card : ℂ) *
      ∑ b : {i // i ∈ B} → Fin q, ∑ c : {i // i ∈ (A ∪ B)ᶜ} → Fin q,
        conj (x (asm A B (fun i => u i) b c)) * y (asm A B (fun i => v i) b c) := by
  classical
  rw [corr, ← Equiv.sum_comp (sitesEquiv A B hAB).symm
    (fun w => conj (x (glue A u w)) * y (glue A v w))]
  show (∑ t : (_ × _ × _), conj (x (glue A u (asm A B t.1 t.2.1 t.2.2)))
      * y (glue A v (asm A B t.1 t.2.1 t.2.2))) = _
  simp only [glue_A, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp

