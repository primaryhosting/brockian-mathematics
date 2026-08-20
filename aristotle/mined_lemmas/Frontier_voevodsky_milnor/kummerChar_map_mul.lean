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

theorem kummerChar_map_mul (h2 : (2 : F) ≠ 0) {c : F} {r : SeparableClosure F}
    (hr : r ^ 2 = algebraMap F (SeparableClosure F) c) (σ τ : absoluteGaloisGroup F) :
    kummerChar F r (σ * τ) = kummerChar F r σ + kummerChar F r τ := by
  by_cases hr0 : r = 0
  · subst hr0
    simp [kummerChar]
  have hneg : -r ≠ r := neg_ne_self_of_ne_zero F h2 hr0
  have hmul : (σ * τ) r = σ (τ r) := rfl
  rcases galois_fix_or_neg F hr σ with hs | hs <;> rcases galois_fix_or_neg F hr τ with ht | ht
  · rw [(kummerChar_eq_zero_iff F r _).2 (by rw [hmul, ht, hs]),
      (kummerChar_eq_zero_iff F r σ).2 hs, (kummerChar_eq_zero_iff F r τ).2 ht, add_zero]
  · rw [kummerChar_eq_one_of_ne F (show (σ * τ) r ≠ r by rw [hmul, ht, map_neg, hs]; exact hneg),
      (kummerChar_eq_zero_iff F r σ).2 hs,
      kummerChar_eq_one_of_ne F (show τ r ≠ r by rw [ht]; exact hneg), zero_add]
  · rw [kummerChar_eq_one_of_ne F (show (σ * τ) r ≠ r by rw [hmul, ht, hs]; exact hneg),
      (kummerChar_eq_zero_iff F r τ).2 ht,
      kummerChar_eq_one_of_ne F (show σ r ≠ r by rw [hs]; exact hneg), add_zero]
  · rw [(kummerChar_eq_zero_iff F r _).2 (by rw [hmul, ht, map_neg, hs, neg_neg]),
      kummerChar_eq_one_of_ne F (show σ r ≠ r by rw [hs]; exact hneg),
      kummerChar_eq_one_of_ne F (show τ r ≠ r by rw [ht]; exact hneg)]
    decide

/-- The Kummer character of a product of square roots is the sum of the characters. -/
