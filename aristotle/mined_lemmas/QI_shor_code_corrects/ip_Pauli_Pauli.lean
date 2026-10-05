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

lemma ip_pauli_pauli (x z x' z' : Bas) (u v : Bas → ℂ) :
    ip (PauliOp x z u) (PauliOp x' z' v)
      = (sgnb (bxorb z z') x : ℂ) * ip u (PauliOp (bxorb x x') (bxorb z z') v) := by
  set w := bxorb z z' with hw
  set Φ : Bas → ℂ :=
    fun b => (sgnb w b : ℂ) * ((starRingEnd ℂ) (u (bxorb x b)) * v (bxorb x' b)) with hΦ
  have hL : ip (PauliOp x z u) (PauliOp x' z' v) = ∑ b : Bas, Φ b := by
    simp only [ip, PauliOp, hΦ]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hs : ((sgnb w b : ℤ) : ℂ) = ((sgnb z b : ℤ) : ℂ) * ((sgnb z' b : ℤ) : ℂ) := by
      rw [hw, ← sgnb_mul]; push_cast; ring
    rw [map_mul, hs]
    simp only [map_intCast]
    ring
  have hre : ∑ b : Bas, Φ b = ∑ b : Bas, Φ (bxorb x b) :=
    (Fintype.sum_equiv (xorEquiv x) (fun b => Φ (bxorb x b)) Φ (fun _ => rfl)).symm
  have hval : ∀ b : Bas, Φ (bxorb x b)
      = (sgnb w x : ℂ) * ((sgnb w b : ℂ) * ((starRingEnd ℂ) (u b) * v (bxorb (bxorb x x') b))) := by
    intro b
    have h1 : bxorb x (bxorb x b) = b := bxorb_involutive x b
    have h2 : bxorb x' (bxorb x b) = bxorb (bxorb x x') b := bxorb_left_comm x x' b
    have h3 : ((sgnb w (bxorb x b) : ℤ) : ℂ) = ((sgnb w x : ℤ) : ℂ) * ((sgnb w b : ℤ) : ℂ) := by
      rw [sgnb_xor_arg]; push_cast; ring
    simp only [hΦ, h1, h2, h3]
    ring
  rw [hL, hre]
  simp only [hval]
  rw [← Finset.mul_sum]
  congr 1
  simp only [ip, PauliOp]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ## Arbitrary single-qubit errors -/

/-- Change the value of the qubit `q` in the basis state `b` to `v`. -/
