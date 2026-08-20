import Mathlib

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including module
docstrings, so the header above appears immediately after the single `import Mathlib`.)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Overview

This file formalises the statement of the *Milnor conjecture* (a theorem of Voevodsky):
for a field `F` of characteristic `≠ 2` the mod-`2` Milnor K-theory of `F` is isomorphic to the
mod-`2` (continuous) Galois cohomology of `F`,
`k^M_n(F) ≅ H^n(Gal(F_sep/F), ℤ/2)`.

We build both sides from scratch:

* `Frontier.MilnorKMod2 F n`, the degree-`n` part of mod-`2` Milnor K-theory, presented as the
  free `ℤ/2`-vector space on `n`-tuples of units of `F` modulo multilinearity and the Steinberg
  relation;
* `Frontier.contCohomologyMod2 G n`, the continuous (inhomogeneous) cochain cohomology of a
  topological group `G` with coefficients in the trivial module `ℤ/2`, applied to the absolute
  Galois group `Gal(F_sep/F)` equipped with the Krull topology.

`Frontier.MilnorConjecture F` is the resulting statement, and the target theorem
`Frontier.voevodsky_milnor` records the parts that are proved here:

1. the base case `n = 0`, for *every* field;
2. the full conjecture for separably closed fields of characteristic `≠ 2`;
3. a Lean-checked reduction of the degree-one case to Kummer theory: the degree-one part of
   mod-`2` Milnor K-theory is `Fˣ/(Fˣ)²`, so degree-one Milnor follows from the statement that the
   Kummer map `Fˣ/(Fˣ)² → H¹(Gal(F_sep/F), ℤ/2)` is an isomorphism.
-/

universe u

namespace Frontier

/-! ## Mod-2 Milnor K-theory -/

section MilnorK

variable (F : Type u) [Field F]

/-- The defining relations of mod-`2` Milnor K-theory in degree `n`, as a subset of the free
`ℤ/2`-vector space on `n`-tuples of units: multilinearity in each slot, and the Steinberg
relation `{a₁, …, aₙ} = 0` whenever `aᵢ + a_j = 1` for some `i ≠ j`. -/

theorem cochainD_comp_cochainD (n : ℕ) (f : (Fin n → G) → ZMod 2) :
    cochainD G (n + 1) (cochainD G n f) = 0 := by
  have hneg : ∀ m : ℕ, ((-1 : ULift.{u} (ZMod 2))) ^ m = 1 := fun m => by
    rw [show (-1 : ULift.{u} (ZMod 2)) = 1 from by decide, one_pow]
  have hd : ∀ (m : ℕ) (f : (Fin m → G) → ZMod 2) (g : Fin (m + 1) → G),
      (inhomogeneousCochains.d (Rep.trivial (ULift.{u} (ZMod 2)) G (ULift.{u} (ZMod 2))) m).hom
        (fun x => (ULift.up (f x) : ULift.{u} (ZMod 2))) g = ULift.up (cochainD G m f g) := by
    intro m f g
    rw [inhomogeneousCochains.d_hom_apply]
    simp only [hneg, one_smul, cochainD_apply]
    rw [show (ULift.up (f (fun i => g i.succ) + ∑ j : Fin (m + 1),
          f (Fin.contractNth j (· * ·) g)) : ULift.{u} (ZMod 2)) =
        ULift.up (f (fun i => g i.succ)) +
          ULift.up (∑ j : Fin (m + 1), f (Fin.contractNth j (· * ·) g)) from rfl]
    congr 1
    exact (map_sum (AddEquiv.ulift (α := ZMod 2)).symm _ _).symm
  have h0 := groupCohomology.inhomogeneousCochains.d_comp_d (k := ULift.{u} (ZMod 2)) (G := G) n
      (Rep.trivial (ULift.{u} (ZMod 2)) G (ULift.{u} (ZMod 2)))
  funext g
  have h1 := congrFun (congrArg (fun (m : ModuleCat.of _ _ ⟶ ModuleCat.of _ _) => m.hom
      (fun x => (ULift.up (f x) : ULift.{u} (ZMod 2)))) h0) g
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero] at h1
  rw [funext (hd n f)] at h1
  rw [hd (n + 1) (cochainD G n f) g] at h1
  exact congrArg ULift.down h1

/-- The space of continuous `n`-cochains. -/
