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

def Statistics.sign : Statistics → ℂ
  | .bose => 1
  | .fermi => -1

/-- A Wightman-type quantum field theory of a field of spin `j` (recorded through
`twoSpin = 2j : ℕ`) with a prescribed statistics, given by its smeared field operators on a
complex inner product space `H` of states, together with the structural axioms used in the
proof of the spin–statistics theorem. -/
structure WightmanTheory (T : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The smeared field operator `phi f` associated with a test function `f`. -/
  phi : T → H →ₗ[ℂ] H
  /-- The vacuum state. -/
  vacuum : H
  /-- Complex conjugation of test functions; `phi (conj f)` is the adjoint of `phi f`. -/
  conj : T → T
  /-- Spacelike separation of the supports of two test functions. -/
  Spacelike : T → T → Prop
  /-- Twice the spin of the field. -/
  twoSpin : ℕ
  /-- The statistics obeyed by the field. -/
  statistics : Statistics
  /-- Hermiticity: `phi (conj f)` is the adjoint of `phi f`. -/
  hermitian : ∀ (f : T) (x y : H), inner ℂ (phi f x) y = inner ℂ x (phi (conj f) y)
  /-- Locality: at spacelike separation the fields commute or anticommute according to the
  assumed statistics. -/
  locality : ∀ f g, Spacelike f g → ∀ x, phi f (phi g x) = statistics.sign • phi g (phi f x)
  /-- Weak local commutativity at Jost points, the consequence of Lorentz covariance of a
  spin-`j` field and of the analyticity of the Wightman functions. -/
  wlc : ∀ f g, Spacelike f g →
      (inner ℂ vacuum (phi f (phi g vacuum)) : ℂ)
        = (-1 : ℂ) ^ twoSpin * inner ℂ vacuum (phi g (phi f vacuum))
  /-- Analytic continuation (edge of the wedge): a two-point function vanishing at all
  spacelike separations vanishes identically. -/
  analyticContinuation :
      (∀ f g, Spacelike f g → (inner ℂ vacuum (phi f (phi g vacuum)) : ℂ) = 0) →
      ∀ f g, (inner ℂ vacuum (phi f (phi g vacuum)) : ℂ) = 0

variable {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two-point Wightman function of the vacuum, `W(f,g) = ⟪Ω, φ(f) φ(g) Ω⟫`. -/
