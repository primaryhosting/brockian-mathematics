/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

noncomputable section

/-- Pauli `X` gate. -/

theorem encode_inner (a b c d : Bool) :
    ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (encode a b p) * encode c d p =
      if (a, b) = (c, d) then 1 else 0 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, encode_apply]
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [pauli, sx, sz, conj_invSqrt2, invSqrt2_mul_self, mul_comm] <;>
    ring

/-- **Superdense coding transmits two classical bits.**
The four encodings of the two-bit messages are pairwise distinct states of the
two-qubit system, i.e. the encoding map is injective on the four messages. -/
