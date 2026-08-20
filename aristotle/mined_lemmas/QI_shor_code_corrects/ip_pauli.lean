/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

lemma ip_pauli (x z x' z' : Bits) (a b : Bool) :
    ip (pauli x z (psi a)) (pauli x' z' (psi b))
      = (1 / 8 : ℂ)
        * ((∑ v : Bits, chi (bxor z z') v * f a (bxor v x) * f b (bxor v x') : ℤ) : ℂ) := by
  unfold ip pauli psi
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [chi_bxor_left]
  simp only [map_mul, Complex.conj_ofReal, map_intCast]
  push_cast
  rw [← nrm_sq_complex]
  ring

/-! ## Knill–Laflamme conditions for Pauli errors -/

