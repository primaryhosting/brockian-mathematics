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

theorem shor_code_identity_error (k j : Fin 3) (a : Bool) :
    ip (act (fun p q => if p = q then 1 else 0) k j (cw a))
      (act (fun p q => if p = q then 1 else 0) k j (cw a)) = 1 := by
  rw [act_id, shor_codewords_orthonormal]
  simp

end QI

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

