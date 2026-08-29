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

def colourStab (f : P → C) : Subgroup G where
  carrier := {h | ∀ p, f (h • p) = f p}
  one_mem' := by intro p; simp
  mul_mem' := by
    intro a b ha hb p
    rw [mul_smul, ha, hb]
  inv_mem' := by
    intro a ha p
    have := ha (a⁻¹ • p)
    rwa [smul_inv_smul, eq_comm] at this

/-- A colouring fixed by `g` is constant along the `⟨g⟩`-orbits of the positions. -/
