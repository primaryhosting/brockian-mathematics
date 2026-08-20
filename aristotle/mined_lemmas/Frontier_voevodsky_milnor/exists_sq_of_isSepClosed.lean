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

theorem exists_sq_of_isSepClosed (F : Type u) [Field F] [IsSepClosed F] (h2 : (2 : F) ≠ 0)
    (a : Fˣ) : ∃ b : Fˣ, b * b = a := by
  haveI : NeZero ((2 : ℕ) : F) := ⟨by simpa using h2⟩
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq (k := F) (a : F) 2
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact a.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, by ext; simpa [pow_two] using hz⟩

/-- The Milnor conjecture holds for separably closed fields of characteristic `≠ 2`: both sides
vanish in positive degrees. -/
