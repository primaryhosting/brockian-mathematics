/-
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The eight Thurston geometries

We formalize a *model geometry* as a topological space `X` together with a group `G`
acting on `X` by homeomorphisms, transitively.  A closed 3-manifold `M` is *geometric*,
modelled on `(X, G)`, when `M` is homeomorphic to a quotient `X / Γ` for a subgroup
`Γ ≤ G` acting freely and properly discontinuously.

The eight Thurston geometries are realized below by concrete model spaces:

* `E³`      : `ℝ³` acted on by translations;
* `S³`      : the unit sphere in `ℝ⁴` acted on by linear isometries;
* `H³`      : the solvable Lie group `ℝ² ⋊ ℝ` (`t` acting by `e^t` on both factors),
              which carries a left invariant metric of constant curvature `-1`;
* `S² × ℝ`  : the unit sphere in `ℝ³` times `ℝ`;
* `H² × ℝ`  : the group `(ℝ ⋊ ℝ) × ℝ`, the affine group of the line (a model of `H²`)
              times `ℝ`;
* `SL(2,ℝ)~`: the universal cover of `PSL(2,ℝ)`, realized as the group of lifts to `ℝ`
              of the projective action of `SL(2,ℝ)` on directions of `ℝ²`;
* `Nil`     : the Heisenberg group;
* `Sol`     : the solvable group `ℝ² ⋊ ℝ` (`t` acting by `e^t`, `e^{-t}`).

In each case the group of the geometry is taken to be a transitive group of isometries
of the model space (for the Lie group models: the group acting on itself by left
translations); we do not verify maximality of these groups, which is what singles out
the eight geometries among all homogeneous 3-dimensional spaces.
-/

/-- Labels for the eight Thurston geometries. -/
inductive ThurstonGeometry
  | euclidean
  | spherical
  | hyperbolic
  | sphereProdLine
  | hyperbolicProdLine
  | slTwoTilde
  | nil
  | sol
  deriving DecidableEq, Fintype, Repr

/-! ### Euclidean 3-space as a group -/

/-- Euclidean 3-space, viewed as the group of its own translations. -/

lemma isOpenMap_proj (Γ : Subgroup mg.G) : IsOpenMap (mg.proj Γ) := by
  intro U hU
  have hpre : (mg.proj Γ) ⁻¹' (mg.proj Γ '' U)
      = ⋃ γ : Γ, (fun x => mg.act ((γ : mg.G)⁻¹) x) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨u, hu, heq⟩
      obtain ⟨γ, hγ, hgu⟩ := Quotient.exact heq
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
      simp only [Set.mem_preimage]
      rw [← hgu, mg.act_inv]
      exact hu
    · intro hx
      obtain ⟨γ, hγ⟩ := Set.mem_iUnion.1 hx
      exact ⟨mg.act ((γ : mg.G)⁻¹) x, hγ,
        mg.proj_eq_proj (γ : mg.G) γ.2 (mg.act_inv' (γ : mg.G) x)⟩
  have hopen : IsOpen ((mg.proj Γ) ⁻¹' (mg.proj Γ '' U)) := by
    rw [hpre]
    exact isOpen_iUnion fun γ => hU.preimage (mg.act_continuous _)
  exact (isQuotientMap_quotient_mk' (s := mg.orbitSetoid Γ)).isOpen_preimage.mp hopen

end ModelGeometry

/-- `M` admits a geometric structure modelled on the model geometry `mg`:
`M` is homeomorphic to a quotient of the model space by a subgroup of the group of the
geometry acting freely and properly discontinuously. -/
