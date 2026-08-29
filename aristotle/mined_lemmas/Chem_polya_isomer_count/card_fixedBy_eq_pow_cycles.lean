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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

-- The skeleton symmetry group acts on colourings (substitution patterns)
-- `P → C` of the positions `P` by `(g • f) p = f (g⁻¹ • p)`.
attribute [local instance] arrowAction

variable {G P C : Type*} [Group G] [MulAction G P]

/-- The subgroup of symmetries that leave a given colouring `f` pointwise unchanged,
in the sense that `f (h • p) = f p` for every position `p`. -/

theorem card_fixedBy_eq_pow_cycles [Finite P] (g : G) :
    Nat.card (MulAction.fixedBy (P → C) g)
      = Nat.card C ^ Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) P)) := by
  rw [Nat.card_congr (fixedColouringEquiv (C := C) g), Nat.card_fun]

/-- **Pólya / Burnside isomer count.**

Let a finite symmetry group `G` act on the set `P` of substitution positions of a molecular
skeleton, and let `C` be the (finite) set of available substituents.  Two substitution patterns
`P → C` describe the same isomer exactly when they lie in the same `G`-orbit.  Then the number of
isomers, multiplied by the order of the symmetry group, equals the Pólya cycle-index sum
`∑_{g ∈ G} |C| ^ c(g)`, where `c(g)` is the number of cycles (`⟨g⟩`-orbits) of `g` on the
positions.

This is Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) combined
with the evaluation of the fixed-point counts (`card_fixedBy_eq_pow_cycles`). -/
