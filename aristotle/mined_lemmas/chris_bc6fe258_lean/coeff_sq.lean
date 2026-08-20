import Mathlib

/-!
# Superdense coding

Alice and Bob share the maximally entangled Bell pair
`|Φ+⟩ = (|00⟩ + |11⟩)/√2` (Alice holds the first qubit, Bob the second).
To send two classical bits `(a, b)` Alice applies the local unitary
`X^a Z^b` to *her* qubit only, i.e. the operator `X^a Z^b ⊗ I` acts on the pair,
and she then sends that single qubit to Bob.

We show that the four resulting two–qubit states are orthonormal, hence perfectly
distinguishable by Bob, and in particular that the encoding map is injective on
the four two–bit messages: two classical bits are transmitted by sending one
qubit.
-/

namespace QC

open Matrix
open scoped Kronecker

/-- A two–qubit state vector, indexed by a pair of bits. -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Pauli `X` matrix. -/

private theorem coeff_sq : (((Real.sqrt 2 : ℝ)) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [inv_pow, h]
  norm_num

/-- Explicit entries: `(U ⊗ I)|Φ+⟩` has entries `U i j / √2`. -/
