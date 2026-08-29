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

lemma constant_on_zpowers_orbits {g : G} {f : P → C} (hf : g • f = f)
    (h : G) (hh : h ∈ Subgroup.zpowers g) (p : P) : f (h • p) = f p := by
  have hg : g ∈ colourStab (C := C) f := by
    intro q
    have : f (g⁻¹ • (g • q)) = f (g • q) := congrFun hf (g • q)
    rwa [inv_smul_smul, eq_comm] at this
  exact (Subgroup.zpowers_le.mpr hg) hh p

/-- **Pólya's key counting step.**  The colourings fixed by a symmetry `g` are exactly the
colourings of the set of cycles (`⟨g⟩`-orbits) of `g` on the positions. -/
