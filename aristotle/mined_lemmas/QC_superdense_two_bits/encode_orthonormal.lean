import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
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

namespace QC

/-- A two-qubit state: `ψ (i, j)` is the amplitude of the basis state `|i⟩ ⊗ |j⟩`.
The first factor is Alice's qubit, the second is Bob's. -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Bell state `(|00⟩ + |11⟩)/√2`, shared in advance between Alice and Bob. -/

theorem encode_orthonormal (a b a' b' : Bool) :
    inner2 (encode a b) (encode a' b') = if (a, b) = (a', b') then 1 else 0 := by
  have hc := half_of_sqrt_two
  simp only [inner2, Fintype.sum_prod_type, Fin.sum_univ_two, encode_apply, map_mul,
    Complex.conj_ofReal]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp only [encGate_ff, encGate_tf, encGate_ft, encGate_tt, pauliX, pauliZ] <;>
    norm_num [Matrix.one_apply] <;>
    ring_nf <;>
    linear_combination (norm := (push_cast [Complex.ofReal_inv]; ring_nf)) (2 : ℂ) * hc

#print axioms QC.superdense_two_bits
#print axioms QC.encode_orthonormal
#print axioms QC.encGate_unitary

end QC

