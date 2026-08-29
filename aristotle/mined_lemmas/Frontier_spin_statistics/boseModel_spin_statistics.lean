import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Overview

We formalize the *spin–statistics connection* in the algebraic form in which it is proved in
the Wightman framework (Streater–Wightman, Theorem 4-10): a relativistic quantum field which
obeys the *wrong* connection between spin and statistics annihilates the vacuum, hence is
trivial.  Equivalently, for a nontrivial field the statistics sign `ε` (`+1` for Bose,
`-1` for Fermi commutation relations at spacelike separation) must equal `(-1) ^ (2j)`,
where `j` is the spin: integer spin forces Bose statistics and half-integer spin forces
Fermi statistics.

The structure `Frontier.WightmanTheory` bundles the inputs of the argument:

* the fields `phi f` are operators on a complex inner product space, indexed by (smeared)
  test functions `f`, with `conj f` the test function implementing the adjoint;
* `hermitian`: `phi (conj f)` is the adjoint of `phi f`;
* `locality`: at spacelike separation the fields commute (`ε = 1`) or anticommute (`ε = -1`),
  according to the assumed statistics;
* `wlc`: *weak local commutativity* at Jost points, `W(f,g) = (-1)^(2j) W(g,f)`.  This is the
  standard consequence of Lorentz covariance of a spin-`j` field together with the analyticity
  of the Wightman functions;
* `analyticContinuation`: the edge-of-the-wedge/analytic-continuation input, namely that a
  two-point Wightman function vanishing for all spacelike-separated arguments vanishes
  identically.

The theorem `Frontier.spin_statistics` is then a fully Lean-checked reduction: from these
axioms and nontriviality of the field, the spin–statistics relation `ε = (-1)^(2j)` follows.

Two concrete toy models (`Frontier.boseModel`, `Frontier.fermiModel`) are constructed at the
end of the file, showing that the axiom system is consistent and that both the Bose case
(`2j` even) and the Fermi case (`2j` odd) really occur.
-/

/-- The two possible statistics of a field: commuting (Bose) or anticommuting (Fermi)
at spacelike separation. -/
inductive Statistics where
  | bose
  | fermi
deriving DecidableEq, Repr

/-- The sign `ε` occurring in the (anti)commutation relations: `+1` for Bose, `-1` for Fermi. -/

theorem boseModel_spin_statistics :
    boseModel.statistics.sign = (-1 : ℂ) ^ boseModel.twoSpin :=
  spin_statistics boseModel boseModel_nontrivial

/-- The two-dimensional "Clifford" toy model of a spin-`1/2` field: test functions are
vectors `f ∈ ℝ²`, the field is `φ(f) = f₁σ₁ + f₂σ₂`, spacelike separation is orthogonality
of `f` and `g`, and the statistics is Fermi. -/
