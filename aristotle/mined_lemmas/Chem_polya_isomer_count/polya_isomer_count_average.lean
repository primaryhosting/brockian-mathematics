/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pólya / Burnside isomer count

Counting substitution isomers on a symmetric molecular skeleton: the number of isomers is the
Burnside/Pólya cycle-index average `(1/|G|) ∑_{g ∈ G} |Sub| ^ (number of cycles of g)`.

The key ingredients are Mathlib's Burnside lemma
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, together with the identification of
the colourings fixed by a symmetry `g` with arbitrary functions on the set of cycles of `g`.
-/

namespace Chem

open MulAction

/- The action of the skeleton's symmetry group `G` on colourings (substitution patterns)
`Pos → Sub` is given by `(g • c) x = c (g⁻¹ • x)`. -/
attribute [local instance] arrowAction

section

variable {G Pos Sub : Type*} [Group G] [MulAction G Pos]

/-- The subgroup of symmetries that preserve a given colouring `c`, i.e. the set of `k : G`
with `c (k • x) = c x` for all positions `x`. -/

theorem polya_isomer_count_average [Nonempty G] :
    (Nat.card (Quotient (orbitRel G (Pos → Sub))) : ℚ)
      = (1 / (Nat.card G : ℚ)) *
        ∑ g : G, (Nat.card Sub : ℚ) ^ Nat.card (Quotient (orbitRel (Subgroup.zpowers g) Pos)) := by
  have hG : (Nat.card G : ℚ) ≠ 0 := by
    have : 0 < Nat.card G := Nat.card_pos
    positivity
  have h := congrArg (fun n : ℕ => (n : ℚ)) (polya_isomer_count (G := G) (Pos := Pos) (Sub := Sub))
  push_cast at h
  field_simp
  linarith [h]

end

end Chem

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

