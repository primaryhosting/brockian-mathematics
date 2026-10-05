/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/

lemma ipf_expand (α β : Fin 4 → ℂ) (f g : Fin 4 → Amp) :
    ipf (∑ k : Fin 4, α k • f k) (∑ l : Fin 4, β l • g l)
      = ∑ k : Fin 4, ∑ l : Fin 4, (starRingEnd ℂ) (α k) * β l * ipf (f k) (g l) := by
  rw [ipf_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ipf_smul_left, ipf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ipf_smul_right]
  ring

/-- An operator on the 9-qubit register is an *arbitrary single-qubit error* if it acts as an
arbitrary `2 × 2` matrix `a·I + b·X + c·Y + d·Z` on one qubit and as the identity elsewhere. -/
