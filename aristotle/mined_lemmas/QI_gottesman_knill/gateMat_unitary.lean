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

lemma gateMat_unitary {n : ℕ} (g : Gate n) : (gateMat g)ᴴ * gateMat g = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  cases g with
  | H j =>
      have hf : ∀ c : Bits n, ¬(∀ i, i ≠ j → c i = a i) →
          (starRingEnd ℂ) (gateMat (Gate.H j) c a) * gateMat (Gate.H j) c b = 0 := by
        intro c hc
        have h0 : gateMat (Gate.H j) c a = 0 := by rw [gateMat_H_apply, if_neg hc]
        rw [h0]; simp
      rw [sum_pair_support j a _ hf]
      by_cases hab : ∀ i, i ≠ j → a i = b i
      · have hupda : ∀ v : Bool, (∀ i, i ≠ j → (Function.update a j v) i = a i) := by
          intro v i hi; rw [Function.update_of_ne hi]
        have hupdb : ∀ v : Bool, (∀ i, i ≠ j → (Function.update a j v) i = b i) := by
          intro v i hi; rw [Function.update_of_ne hi]; exact hab i hi
        simp only [gateMat_H_apply, if_pos (hupda false), if_pos (hupda true),
          if_pos (hupdb false), if_pos (hupdb true), Function.update_self]
        have hone : (1 : Matrix (Bits n) (Bits n) ℂ) a b = if a j = b j then 1 else 0 := by
          rw [Matrix.one_apply]
          by_cases h : a j = b j
          · rw [if_pos h, if_pos]
            funext i
            by_cases hi : i = j
            · subst hi; exact h
            · exact hab i hi
          · rw [if_neg h, if_neg]
            intro hh; exact h (congrFun hh j)
        rw [hone]
        cases hja : a j <;> cases hjb : b j <;>
          simp only [Bool.and_false, Bool.and_true, if_true, map_mul, map_one, map_neg,
            Complex.conj_ofReal, ← Complex.ofReal_inv] <;>
          simp [sqrt2_inv_sq] <;> norm_num
      · have hane : a ≠ b := fun h => hab (fun i _ => by rw [h])
        have hnb : ∀ v : Bool, ¬ (∀ i, i ≠ j → (Function.update a j v) i = b i) := by
          intro v h; exact hab (fun i hi => by rw [← h i hi, Function.update_of_ne hi])
        simp only [gateMat_H_apply]
        rw [if_neg (hnb false), if_neg (hnb true), Matrix.one_apply_ne hane]
        ring
  | S j =>
      rw [Finset.sum_eq_single a]
      · by_cases hab : a = b
        · subst hab
          simp only [gateMat_S_apply, Matrix.one_apply_eq]
          cases h : a j <;> simp [Complex.conj_I, Complex.I_mul_I]
        · simp only [gateMat_S_apply, if_neg hab, mul_zero]
          rw [Matrix.one_apply_ne hab]
      · intro d _ hd
        simp only [gateMat_S_apply, if_neg hd, map_zero, zero_mul]
      · intro hh; exact absurd (Finset.mem_univ _) hh
  | CX c t h =>
      rw [Finset.sum_eq_single (flipT c t a)]
      · simp only [gateMat_CX_apply, if_true, map_one, one_mul]
        by_cases hab : a = b
        · subst hab; rw [if_pos rfl, Matrix.one_apply_eq]
        · rw [if_neg (fun hh => hab (flipT_inj h hh)), Matrix.one_apply_ne hab]
      · intro d _ hd
        simp only [gateMat_CX_apply, if_neg hd, map_zero, zero_mul]
      · intro hh; exact absurd (Finset.mem_univ _) hh

/-! ### Correctness of the tableau update -/

/-- The `𝔽₂` inner product identity behind the `CNOT` tableau rule. -/
