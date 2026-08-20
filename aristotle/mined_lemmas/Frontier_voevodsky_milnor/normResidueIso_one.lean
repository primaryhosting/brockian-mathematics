import Mathlib

/-!
# Voevodsky Milnor: definitions and supporting results

Supporting development for `Frontier.voevodsky_milnor` (see `RequestProject/Main.lean`):
mod-2 Milnor K-theory, mod-2 Galois cohomology, the statement of the Milnor conjecture, the
degree-zero base case, the separably closed case, and the degree-one identifications.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false

namespace Frontier

/-!
## Mod-2 Milnor K-theory

For a field `F`, the `n`-th Milnor K-group `K^M_n(F)` is the degree-`n` part of the quotient of
the tensor algebra of the abelian group `Fˣ` by the Steinberg relations `a ⊗ (1 - a) = 0`.
Reducing mod 2, `k^M_n(F) = K^M_n(F)/2` is therefore the quotient of the free `ZMod 2`-module on
`n`-tuples of units by
* multilinearity in each slot, and
* the Steinberg relations (in adjacent slots).

This is the definition used below.
-/

section Milnor

variable (F : Type) [Field F]

/-- The defining relations of mod-2 Milnor K-theory in degree `n`: multilinearity in each slot,
and the Steinberg relation `{a, 1 - a} = 0` in adjacent slots. -/

theorem normResidueIso_one (h2 : (2 : F) ≠ 0) : NormResidueIso F 1 :=
  (normResidueIso_one_iff_kummer F).2 ⟨kummerEquiv h2⟩

end Surjectivity

end Frontier

/-
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` commands to precede
-- any module docstring; the same header is repeated as a module docstring below.)

import RequestProject.Kummer

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- **Voevodsky's Milnor conjecture.**

`NormResidueIso F n` is the statement that mod-2 Milnor K-theory `k^M_n(F)` agrees with mod-2
Galois cohomology `H^n(F, ℤ/2)` (continuous cochain cohomology of the absolute Galois group with
trivial `ℤ/2`-coefficients).  We prove:

1. the base case `n = 0`, for an arbitrary field;
2. the case `n = 1`, for an arbitrary field of characteristic `≠ 2` (this is Kummer theory,
   proved here from scratch: `k^M_1(F) = Fˣ/(Fˣ)²` is the group of continuous characters
   `Gal(F^sep/F) → ℤ/2`); and
3. the full statement, in all degrees, for separably closed fields of characteristic `≠ 2`. -/
