/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is reproduced verbatim as a module docstring below; Lean 4 requires
-- `import` commands to precede any module docstring.)

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

Hastings' area law states that the ground state of a gapped local Hamiltonian on a
one-dimensional chain has entanglement entropy across any cut bounded by a constant,
independent of the length of the chain and of the position of the cut.  The mechanism
behind the theorem is that such a ground state is (approximated by) a *finitely
correlated state* / *matrix product state* of bounded bond dimension `D`; a state with
a bond dimension `D` across a cut has Schmidt rank at most `D`, hence entanglement
entropy at most `log D`.

Here we formalize this final, mathematical content of the area law: for a matrix
product state on a chain of `k + m` sites built from `D × D` transfer matrices, the
von Neumann entropy of the reduced density matrix of the first `k` sites is at most
`log D`, *uniformly in `k` and `m`*.  This is the quantitative area-law bound: a
constant, independent of the subsystem size and of the total system size (in one
dimension the boundary of an interval consists of a bounded number of points, so a
constant bound *is* an area law).  The physical input of Hastings' theorem — that a
gapped local Hamiltonian has a ground state of this form — is an approximation
statement about Hamiltonians and is not part of the formalization below.

The two mathematical ingredients that are proved from scratch are:

* `Phys.entropy_le_log_of_card_support_le` — the maximum-entropy bound: a probability
  vector supported on at most `D` outcomes has Shannon entropy at most `log D`;
* `Phys.cutMatrix_eq_mul` — the matrix product structure factors the coefficient
  matrix of the state across the cut through a `D`-dimensional space, so the reduced
  density matrix has rank at most `D`.
-/

namespace Phys

open Matrix Finset

/-! ## Shannon entropy and the maximum entropy bound -/

/-- Shannon (von Neumann) entropy of a finite family of numbers,
`H(p) = -∑ pᵢ log pᵢ`. -/

noncomputable def entEntropy {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (M : Matrix α β ℂ) : ℝ :=
  entropy (reducedDensity_isHermitian M).eigenvalues

