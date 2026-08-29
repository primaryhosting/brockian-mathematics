/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace QI

/-! ## Basic types

A computational basis state of one *block* of three qubits is a function `Fin 3 → Bool`;
a computational basis state of the nine qubits of the Shor code is a function
`Fin 3 → Blk`, i.e. three blocks of three qubits.  A qubit is addressed by a pair
`q : Q = Fin 3 × Fin 3` (block index, position inside the block). -/

/-- Computational basis states of one three-qubit block. -/
abbrev Blk := Fin 3 → Bool

/-- Computational basis states of the nine qubits. -/
abbrev Bas := Fin 3 → Blk

/-- Addresses of the nine qubits. -/
abbrev Q := Fin 3 × Fin 3

/-- Bitwise `xor` on a block. -/

lemma ip_cw_pauli_int (s t : Bool) (x z : Bas) :
    ∑ b : Bas, czw s b * sgnb z b * czw t (bxorb x b) = ∏ j, gBlk s t (x j) (z j) := by
  have h1 : (∏ j, gBlk s t (x j) (z j))
      = ∑ b ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset Blk)),
          ∏ j, (fBlk s (b j) * sgnB (z j) (b j) * fBlk t (bxorB (x j) (b j))) := by
    simpa [gBlk] using
      Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset Blk))
        (fun j β => fBlk s β * sgnB (z j) β * fBlk t (bxorB (x j) β))
  rw [h1, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [czw, sgnb, bxorb, ← Finset.prod_mul_distrib]

