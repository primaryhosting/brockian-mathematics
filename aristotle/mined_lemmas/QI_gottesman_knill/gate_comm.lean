/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Gottesman–Knill

We formalise the Gottesman–Knill theorem: a quantum circuit built out of Clifford gates
(Hadamard, phase, CNOT) acting on `n` qubits can be simulated classically with only
`2n + 2` bits of memory and a constant amount of work per gate, in the Heisenberg picture.

The `2^n`-dimensional Hilbert space is modelled as `Bits n → ℂ`, i.e. operators are
matrices indexed by bitstrings `Bits n = Fin n → Bool`.

A Pauli operator is stored as a *tableau row* `(k, x, z)` with `k : ZMod 4` a phase
exponent and `x z : Bits n`; it denotes the operator `i^k X^x Z^z`, whose matrix is
`|b⟩ ↦ i^k (-1)^{z·b} |b ⊕ x⟩`.

The three main ingredients are:

* `QI.gateMat_unitary` : the gate matrices are unitary;
* `QI.gate_conj` : conjugating a Pauli matrix by a Clifford gate matrix is computed
  exactly by the (purely classical, bit-level) tableau update `QI.gateConj`;
* `QI.gateConj_local` : the tableau update only touches the qubits in the gate's support.

Together these give `QI.gottesman_knill`.
-/

namespace QI

/-- Bitstrings of length `n`; these index the computational basis of `n` qubits. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- Bitwise XOR of two bitstrings. -/

lemma gate_comm {n : ℕ} (g : Gate n) (P : Pauli n) :
    P.toMatrix * gateMat g = gateMat g * (gateConj g P).toMatrix := by
  cases g with
  | S j =>
      ext a b
      simp only [gateConj]
      rw [toMatrix_mul_apply, mul_toMatrix_apply, gateMat_S_apply, gateMat_S_apply]
      by_cases h : bxor a P.x = b
      · have ha : a = bxor b P.x := by rw [← h, bxor_bxor_cancel]
        subst ha
        rw [bxor_bxor_cancel, if_pos rfl, if_pos rfl, bdot_eq_off j P.z b, bdot_update_j]
        exact S_scalar P.k (P.x j) (P.z j) (b j) (bdotOff j P.z b)
      · have h2 : ¬ (a = bxor b P.x) := fun hh => h (by rw [hh, bxor_bxor_cancel])
        rw [if_neg h, if_neg h2, mul_zero, zero_mul]
  | H j =>
      ext a b
      simp only [gateConj]
      rw [toMatrix_mul_apply, mul_toMatrix_apply, gateMat_H_apply, gateMat_H_apply]
      have hupd : ∀ i, i ≠ j →
          (bxor b (Function.update P.x j (P.z j))) i = xor (b i) (P.x i) := by
        intro i hi
        show xor (b i) (Function.update P.x j (P.z j) i) = xor (b i) (P.x i)
        rw [Function.update_of_ne hi]
      by_cases h : ∀ i, i ≠ j → (bxor a P.x) i = b i
      · have h2 : ∀ i, i ≠ j → a i = (bxor b (Function.update P.x j (P.z j))) i := by
          intro i hi
          rw [hupd i hi]
          have hb := h i hi
          show a i = xor (b i) (P.x i)
          have bl : ∀ u v w : Bool, xor u v = w → u = xor w v := by decide
          exact bl _ _ _ hb
        rw [if_pos h, if_pos h2, bdot_eq_off j P.z (bxor a P.x),
          bdotOff_congr j (u' := P.z) (v' := b) (fun _ _ => rfl) h,
          bdot_update_j j P.z b (P.x j),
          show (bxor b (Function.update P.x j (P.z j))) j = xor (b j) (P.z j) by
            show xor (b j) (Function.update P.x j (P.z j) j) = xor (b j) (P.z j)
            rw [Function.update_self]]
        exact H_scalar P.k (a j) (b j) (P.x j) (P.z j) (bdotOff j P.z b) _
      · have h2 : ¬ (∀ i, i ≠ j → a i = (bxor b (Function.update P.x j (P.z j))) i) := by
          intro hh
          apply h
          intro i hi
          have hb := hh i hi
          rw [hupd i hi] at hb
          show xor (a i) (P.x i) = b i
          have bl : ∀ u v w : Bool, u = xor w v → xor u v = w := by decide
          exact bl _ _ _ hb
        rw [if_neg h, if_neg h2, mul_zero, zero_mul]
  | CX c t hct =>
      ext a b
      simp only [gateConj]
      rw [toMatrix_mul_apply, mul_toMatrix_apply, gateMat_CX_apply, gateMat_CX_apply]
      have key := CX_x hct b P.x
      by_cases h : bxor a P.x = flipT c t b
      · have ha : a = flipT c t (bxor b (Function.update P.x t (xor (P.x t) (P.x c)))) := by
          rw [← key, ← h, bxor_bxor_cancel]
        rw [if_pos h, if_pos ha, one_mul, mul_one, h, CX_bdot hct P.z b]
      · have h2 : ¬ (a = flipT c t (bxor b (Function.update P.x t (xor (P.x t) (P.x c))))) := by
          intro hh
          apply h
          rw [hh, ← key, bxor_bxor_cancel]
        rw [if_neg h, if_neg h2, mul_zero, zero_mul]

