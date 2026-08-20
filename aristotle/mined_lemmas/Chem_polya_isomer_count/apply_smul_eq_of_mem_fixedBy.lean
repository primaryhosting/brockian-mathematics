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

/-!
# Pólya / Burnside counting of substitution isomers

A "skeleton" is a finite set `X` of substitution sites, carrying an action of a finite
symmetry group `G`.  A *substitution pattern* is a function `X → C` assigning to each site
one of finitely many substituents `C`; two patterns describe the same *isomer* exactly when
they differ by a symmetry of the skeleton, i.e. they lie in the same orbit of the induced
action of `G` on `X → C`.

The main result `Chem.polya_isomer_count` states the Pólya/Burnside cycle-index formula:
the number of isomers, times `|G|`, equals `∑ g : G, |C| ^ (number of cycles of g on X)`,
where the number of cycles of `g` is the number of orbits of the cyclic subgroup `⟨g⟩`
acting on `X`.
-/

namespace Chem

-- If `G` acts on the sites `X`, it acts on substitution patterns `X → C` by
-- `(g • f) x = f (g⁻¹ • x)`.
attribute [local instance] arrowAction

variable {G X C : Type*} [Group G] [MulAction G X]

/-- A pattern fixed by `g` is constant along the orbits of the cyclic subgroup `⟨g⟩`. -/

theorem apply_smul_eq_of_mem_fixedBy {g : G} {f : X → C}
    (hf : f ∈ MulAction.fixedBy (X → C) g) {h : G} (hh : h ∈ Subgroup.zpowers g) (x : X) :
    f (h • x) = f x := by
  have hg : g ∈ MulAction.stabilizer G f := hf
  have hmem : h ∈ MulAction.stabilizer G f :=
    (Subgroup.zpowers_le (H := MulAction.stabilizer G f)).mpr hg hh
  have hfix : h • f = f := hmem
  have key : ∀ a : X, f (h⁻¹ • a) = f a := fun a => congrFun hfix a
  have := key (h • x)
  rwa [inv_smul_smul, eq_comm] at this

/-- Patterns fixed by `g` correspond to arbitrary colourings of the set of `⟨g⟩`-orbits
(the cycles of `g`). -/
