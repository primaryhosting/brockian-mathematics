/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above uses `/- ... -/` rather than `/-! ... -/` because Lean 4 does not allow a
-- module docstring to precede the `import` block.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

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

/-!
## Setting

A bipartite quantum system with finite-dimensional factors `A` (Alice) and `B` (Bob) is modelled
by matrices indexed by `A × B` over `ℂ`; a state is such a matrix `ρ` (no positivity or unit-trace
hypothesis is needed for the result below, so none is imposed).

* `Frontier.ptA ρ` is the partial trace over Alice's factor, i.e. Bob's reduced density matrix.
* `Frontier.extA K` is a local operator `K ⊗ I_B` acting on Alice's side only.
* `Frontier.extB M` is a local operator `I_A ⊗ M` acting on Bob's side only.
* `Frontier.krausA K ρ = ∑ i, (K i ⊗ I) ρ (K i ⊗ I)†` is the most general local quantum
  operation Alice can perform, written in Kraus form; the channel is trace preserving exactly
  when `∑ i, (K i)ᴴ * K i = 1`.

The theorem `Frontier.no_communication` says that any such local operation of Alice leaves Bob's
reduced density matrix *exactly* unchanged, and `Frontier.bob_statistics_unchanged` concludes that
therefore every expectation value `Tr(ρ (I ⊗ M))` of a Bob-local observable is unchanged, so no
information reaches Bob.

Remark on existing Mathlib support: a search of Mathlib turns up no partial-trace or
quantum-channel API (there is no `Matrix.partialTrace` / Kraus-operator development), so the
statement is built from the basic matrix API (`Matrix.mul_apply`, `Matrix.conjTranspose_apply`,
`Matrix.trace`, `Finset.sum_comm`, `Fintype.sum_prod_type`) rather than closed by a single
existing lemma.
-/

namespace Frontier

variable {A B ι : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype ι]

/-- The partial trace over Alice's factor: Bob's reduced density matrix. -/

noncomputable def krausA (K : ι → Matrix A A ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ i, extA (K i) * ρ * (extA (K i))ᴴ

