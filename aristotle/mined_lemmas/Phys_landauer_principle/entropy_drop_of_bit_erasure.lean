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

import Mathlib
/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Phys

/-- Shannon (Gibbs) entropy, in nats, of a finite probability distribution `p`.
Uses the convention `0 * log 0 = 0`, which holds automatically in Mathlib since
`Real.log 0 = 0`. -/

theorem entropy_drop_of_bit_erasure (j : Fin 2) :
    shannonEntropy (fun _ : Fin 2 => (1 : ℝ) / 2) -
      shannonEntropy (fun i : Fin 2 => if i = j then (1 : ℝ) else 0) = Real.log 2 := by
  rw [shannonEntropy_uniform_two, shannonEntropy_pointMass, sub_zero]

/--
**Landauer's principle.**

A logically irreversible operation — here the erasure of one bit, which takes the
memory from the unbiased distribution `(1/2, 1/2)` over its two states to the
deterministic state `j` — must dissipate at least `k T log 2` of heat into the
thermal reservoir at temperature `T`.

The physical input is the Clausius inequality `hClausius`: the heat `Q` released to
a reservoir at temperature `T` is at least `k T` times the entropy decrease of the
system (equivalently, the total entropy of system plus reservoir does not decrease).
The mathematical content proved here is that the entropy decrease of an erased bit
is exactly `log 2` nats, whence `Q ≥ k T log 2`.

With `k` the Boltzmann constant this is the familiar bound `Q ≥ k_B T ln 2`.
No positivity assumptions on `k` and `T` are needed for the implication itself;
that the bound is a genuine positive cost is recorded in `Phys.landauer_bound_pos`.
-/
