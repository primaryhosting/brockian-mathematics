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

theorem twoPoint_eq_zero_of_spacelike (W : WightmanTheory T H)
    (h : W.statistics.sign ≠ (-1 : ℂ) ^ W.twoSpin) :
    ∀ f g, W.Spacelike f g → W.twoPoint f g = 0 := by
  intro f g hfg
  -- Locality gives `W(f,g) = ε · W(g,f)`.
  have h1 : W.twoPoint f g = W.statistics.sign * W.twoPoint g f := by
    simp only [WightmanTheory.twoPoint]
    rw [W.locality f g hfg, inner_smul_right]
  -- Weak local commutativity gives `W(f,g) = (-1)^(2j) · W(g,f)`.
  have h2 : W.twoPoint f g = (-1 : ℂ) ^ W.twoSpin * W.twoPoint g f := W.wlc f g hfg
  have hb : W.twoPoint g f = 0 := by
    have h3 : (W.statistics.sign - (-1 : ℂ) ^ W.twoSpin) * W.twoPoint g f = 0 := by
      linear_combination h1.symm.trans h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) h
    · exact h4
  rw [h1, hb, mul_zero]

/-- **Wrong statistics implies a trivial field.**  If the statistics sign does not match the
spin parity `(-1)^(2j)`, then every smeared field operator annihilates the vacuum. -/
