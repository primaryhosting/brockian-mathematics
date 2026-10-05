/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header comment above uses `/- ... -/` rather than `/-! ... -/`: Lean requires all
-- `import` lines to precede any module docstring, so a `/-!` block cannot open the file.)

import Mathlib

open scoped BigOperators

/-!
# The 9-qubit Shor code corrects an arbitrary single-qubit error

The 9 qubits are grouped into three blocks of three, so a computational basis state of the
register is an element of `Cfg = Blk × Blk × Blk` with `Blk = Bool × Bool × Bool`, and a state
vector is a function `Cfg → ℂ` of amplitudes.

The logical codewords are

* `|0_L⟩ = (|000⟩ + |111⟩)^{⊗3} / (2√2)`,
* `|1_L⟩ = (|000⟩ - |111⟩)^{⊗3} / (2√2)`.

An arbitrary single-qubit error acting on qubit `j` of block `k` is given by an arbitrary
`2 × 2` complex matrix `A : Bool → Bool → ℂ` (no linearity, unitarity or normalization is
assumed).  The main theorem `QI.shor_code_corrects` establishes the Knill–Laflamme
error-correction conditions
`⟨c_a | A† B | c_b⟩ = δ_{a b} · α(A, B)`
for all pairs of single-qubit operators `A`, `B` placed at arbitrary (possibly different) qubits.
Note that `⟨c_a | A† B | c_b⟩ = ⟨A c_a , B c_b⟩`, which is the form used below.  Since every
single-qubit error operator is one of these and error channels are linear, these conditions are
exactly the statement that the code corrects an arbitrary single-qubit error.
-/

namespace QI

/-- Computational basis states of one 3-qubit block. -/
abbrev Blk := Bool × Bool × Bool

/-- Computational basis states of the 9-qubit register, grouped into three blocks. -/
abbrev Cfg := Blk × Blk × Blk

/-- Read qubit `j` of a block. -/

noncomputable def tri (g₁ g₂ g₃ : Blk → ℂ) : Cfg → ℂ :=
  fun w => g₁ w.1 * g₂ w.2.1 * g₃ w.2.2

/-- The normalization constant of the Shor codewords. -/
