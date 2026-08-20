/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
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

namespace Chem

open MulAction

attribute [local instance] arrowAction

section

variable {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [Fintype P] [MulAction G P]
variable {C : Type*} [Fintype C]

/-- Burnside's lemma, phrased with `Nat.card`. -/

lemma card_fixedBy_eq (g : G) :
    Nat.card (fixedBy (P → C) g)
      = Nat.card C ^ Nat.card (orbitRel.Quotient (Subgroup.zpowers g) P) := by
  classical
  rw [Nat.card_congr (fixedByEquivCycleColorings (C := C) g)]
  haveI : Finite (orbitRel.Quotient (Subgroup.zpowers g) P) := Quotient.finite _
  exact Nat.card_fun

/-- **Pólya / Burnside isomer count.**  If a symmetry group `G` acts on the set `P` of
substitution positions of a molecular skeleton, and substituents are drawn from a set `C`
of types, then the number of distinct substitution isomers (i.e. orbits of colorings
`P → C` under the skeleton symmetry) times the order of `G` equals the sum over group
elements `g` of `|C|` raised to the number of cycles of `g` on the positions.  Equivalently,
the isomer count is the average `(1/|G|) ∑_g |C|^{c(g)}`: the Pólya cycle index evaluated
at `x_i = |C|`. -/
