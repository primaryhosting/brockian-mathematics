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

theorem knill_laflamme (i j : Fin 7) (p q : ZMod 2 × ZMod 2) (f g : St)
    (hf : IsStabilized f) (hg : IsStabilized g) :
    ip (errOp (pauliErr i p) f) (errOp (pauliErr j q) g)
      = if pauliErr i p = pauliErr j q then ip f g else 0 := by
  by_cases h : pauliErr i p = pauliErr j q
  · rw [if_pos h, h, errOp, ip_pauli_eq_T, bits_add_self, T_zero_diag]
  · rw [if_neg h, errOp, errOp, ip_pauli_eq_T]
    by_cases hx : ∀ k, dot (row k) (xv (pauliErr i p)) + dot (row k) (xv (pauliErr j q)) = 0
    · by_cases hz : ∀ k, dot (zv (pauliErr i p) + zv (pauliErr j q)) (row k) = 0
      · exact absurd (single_error_sep i j p q hx hz) h
      · push_neg at hz
        obtain ⟨k, hk⟩ := hz
        refine T_eq_zero_of_anticommute (row k) 0 _ _ _ f g (hf k).1 (hg k).1 ?_
        rw [dot_zero_left, dot_zero_left]
        rcases zmod2_cases (dot (zv (pauliErr i p) + zv (pauliErr j q)) (row k)) with h0 | h1
        · exact absurd h0 hk
        · rw [h1]; ring
    · push_neg at hx
      obtain ⟨k, hk⟩ := hx
      refine T_eq_zero_of_anticommute 0 (row k) _ _ _ f g (hf k).2 (hg k).2 ?_
      rw [dot_zero_right]
      rcases zmod2_cases (dot (row k) (xv (pauliErr i p)) +
          dot (row k) (xv (pauliErr j q))) with h0 | h1
      · exact absurd h0 hk
      · rw [add_zero, h1]

/-! ### Main theorem -/

/-- **The 7-qubit Steane code corrects any single-qubit error.**

1. The code space is nontrivial: the logical `|0⟩` state `zeroL` is a nonzero state (of squared
   norm `16`) fixed by all six stabilizer generators.
2. The Knill–Laflamme error-correction condition holds for the set of all single-qubit Pauli
   errors `{I, X, Y, Z}` on any of the seven qubits: for codewords `f, g`,
   `⟪E f, F g⟫ = c (E, F) ⟪f, g⟫` with `c (E, F) = 1` for `E = F` and `0` otherwise.  By the
   Knill–Laflamme theorem this says precisely that the code corrects any single-qubit error.
3. Concretely, the explicit decoder `decodeErr` reconstructs every single-qubit Pauli error
   from its measured stabilizer syndrome. -/
