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
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MulAction

namespace Chem

attribute [local instance] arrowAction

variable {G P C : Type*} [Group G] [MulAction G P]

/-- The subgroup of symmetries that leave a given substitution pattern (colouring) `f`
unchanged pointwise, i.e. `f (h • p) = f p` for all positions `p`. -/

lemma card_fixedBy_colorings (g : G) [Finite P] :
    Nat.card (fixedBy (P → C) g) = Nat.card C ^ cycleCount P g := by
  rw [Nat.card_congr (fixedByEquivCycleFunctions (C := C) g), cycleCount, Nat.card_fun]

/-- **Pólya / Burnside isomer count.**

For a finite symmetry group `G` acting on the positions `P` of a molecular skeleton, the number
of distinct substitution isomers, i.e. the number of orbits of `G` on the colourings `P → C`
(assigning a substituent from `C` to each position), multiplied by the order of `G`, equals the
sum over the symmetries `g ∈ G` of `|C| ^ (number of cycles of g)`.

Equivalently, the isomer count is the cycle-index average
`(1 / |G|) * ∑_{g ∈ G} |C| ^ c(g)`.

The proof is Burnside's lemma, `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`,
combined with the identification of the colourings fixed by `g` with the functions on the
cycles of `g`. -/
