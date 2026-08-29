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

noncomputable def zeroL : Amp := fun b => if isCode b then kappa else 0

/-- The logical one of the Shor code:
`|1_L⟩ = (1/2√2) (|000⟩-|111⟩)(|000⟩-|111⟩)(|000⟩-|111⟩)`. -/
