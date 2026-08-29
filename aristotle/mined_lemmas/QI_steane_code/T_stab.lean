/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Steane `[[7,1,3]]` code corrects any single-qubit error

The Steane code is the CSS code built from the classical `[7,4,3]` Hamming code, whose
parity-check matrix `H` has as its `i`-th column the binary expansion of `i + 1`.  The same
matrix supplies the three `X`-type and the three `Z`-type stabilizer generators.

We work with the honest quantum state space of seven qubits, realised as the `2 ^ 7`-dimensional
complex vector space `Bits → ℂ` of amplitude functions on computational basis states
`Bits = Fin 7 → ZMod 2`, with the Hermitian form `ip f g = ∑ v, conj (f v) * g v`.
For `a b : Bits`, `pauli a b` is the Pauli operator `X(a) Z(b)` (up to an irrelevant global
sign), acting by `(pauli a b f) v = (-1) ^ (b ⬝ v) * f (v + a)`.

The code space is the joint `+1` eigenspace `IsStabilized` of the six stabilizer generators;
it is nontrivial, as witnessed by the logical `|0⟩` state `zeroL`.

The main theorem `QI.steane_code` records three facts:

1. **the code space is nonzero** (`zeroL` is a stabilizer state and `zeroL ≠ 0`);
2. **the Knill–Laflamme error-correction condition** holds for the set of all single-qubit
   Pauli errors: for codewords `f, g` and single-qubit Pauli errors `E, F`,
   `⟪E f, F g⟫ = c (E, F) * ⟪f, g⟫` with `c (E, F) = 1` if `E = F` and `0` otherwise.
   By the Knill–Laflamme theorem this is exactly the statement that the code corrects any
   single-qubit error;
3. **explicit syndrome decoding**: the decoder `decodeErr` reconstructs every single-qubit
   Pauli error from its measured syndrome.
-/

set_option maxRecDepth 40000

namespace QI

/-! ### The classical Hamming parity-check matrix -/

/-- Parity-check matrix of the classical `[7,4,3]` Hamming code: the `i`-th column is the
binary expansion of `i + 1`. -/

theorem T_stab (c d b a1 a2 : Bits) (f g : St)
    (hf : pauli c d f = f) (hg : pauli c d g = g) :
    T b a1 a2 f g = sgn (dot d a1 + dot d a2 + dot b c) * T b a1 a2 f g := by
  have key : ∀ v : Bits, sgn (dot b v) * (star (f (v + a1)) * g (v + a2))
      = sgn (dot d a1 + dot d a2) *
        (sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c))) := by
    intro v
    conv_lhs => rw [← hf, ← hg]
    simp only [pauli, dot_add_right, sgn_add, star_mul', star_sgn]
    have hss := sgn_mul_self (dot d v)
    linear_combination (sgn (dot b v) * sgn (dot d a1) * sgn (dot d a2) *
      (star (f (v + a1 + c)) * g (v + a2 + c))) * hss
  have step1 : T b a1 a2 f g
      = sgn (dot d a1 + dot d a2) *
        ∑ v : Bits, sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => key v
  have step2 : (∑ v : Bits, sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c)))
      = sgn (dot b c) * T b a1 a2 f g := by
    rw [T, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight c)
      (fun v : Bits => sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c)))]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.coe_addRight]
    rw [dot_add_right, sgn_add,
      show v + c + a1 + c = v + a1 by rw [add_right_comm v c a1, add_self_bits],
      show v + c + a2 + c = v + a2 by rw [add_right_comm v c a2, add_self_bits]]
    ring
  rw [sgn_add, mul_assoc, ← step2, ← step1]

/-- If the error difference anticommutes with a stabilizer generator, the overlap vanishes. -/
