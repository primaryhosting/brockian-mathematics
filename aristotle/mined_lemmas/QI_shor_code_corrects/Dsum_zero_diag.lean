/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above
-- is written as a plain block comment; it is repeated as a module docstring below.)

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

/-! ## Setup

The nine qubits of the Shor code are indexed by `Idx = Fin 3 × Fin 3`: the first
component is the block (of the outer phase-flip code), the second the position
inside the block (the inner bit-flip repetition code).

A computational basis state is a configuration `Cfg = Idx → Bool`, and a state
vector is a function `St = Cfg → ℂ` giving the amplitude of each basis state.
-/

/-- Index set of the nine qubits: `(block, position)`. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- A computational basis label for the nine qubits. -/
abbrev Cfg : Type := Idx → Bool

/-- A state vector of the nine-qubit register. -/
abbrev St : Type := Cfg → ℂ

/-- The standard hermitian inner product on the nine-qubit state space,
antilinear in the first argument. -/

lemma Dsum_zero_diag (u : Bool) : Dsum (fun _ : Idx => false) u u = 8 := by
  rw [Dsum_prod]
  have hb : Sblk (fun _ : Fin 3 => false) u u = 2 := by revert u; decide
  simp only [hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-! ## Main theorem -/

/--
**The nine-qubit Shor code corrects an arbitrary single-qubit error.**

`cw false` and `cw true` are the two logical codewords of the Shor code.  For
any two qubits `i, j` and any single-qubit operators `M, N` (arbitrary `2 × 2`
complex matrices, acting on qubit `i` resp. `j` and as the identity elsewhere)
the Knill–Laflamme error-correction conditions hold: there is a constant `c`,
independent of the logical states, with
`⟨M_i w_u , N_j w_v⟩ = ⟨w_u| M_i^† N_j |w_v⟩ = c · δ_{u,v}`.

Since every single-qubit error channel has Kraus operators of this form, and the
conditions are (sesqui)linear in the error operators, this is exactly the
necessary and sufficient criterion for the existence of a recovery operation
correcting an arbitrary error on any one of the nine qubits.
-/
