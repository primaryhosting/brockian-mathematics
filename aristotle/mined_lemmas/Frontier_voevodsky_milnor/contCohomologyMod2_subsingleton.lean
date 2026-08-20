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

theorem contCohomologyMod2_subsingleton [Subsingleton G] {n : ℕ} (hn : 0 < n) :
    Subsingleton (contCohomologyMod2 G n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have key : ∀ z : contCocycles G (m + 1),
      ((z : (Fin (m + 1) → G) → ZMod 2)) ∈ contCoboundaries G (m + 1) := by
    intro z
    set y : (Fin (m + 1) → G) → ZMod 2 := (z : (Fin (m + 1) → G) → ZMod 2) with hy
    set x₀ : Fin (m + 1) → G := fun _ => 1 with hx₀
    have hconst : y = fun _ => y x₀ := funext fun g => congrArg y (Subsingleton.elim _ _)
    have hcoc : cochainD G (m + 1) y = 0 := z.2.1
    rcases Nat.even_or_odd m with he | ho
    · -- `m` even, so `m + 1` is odd and the cocycle condition forces `y = 0`
      have hcast : ((m + 1 : ℕ) : ZMod 2) = 1 := by
        obtain ⟨k, rfl⟩ := he
        push_cast
        rw [show ((k : ZMod 2) + k + 1) = (2 : ZMod 2) * k + 1 by ring, show (2 : ZMod 2) = 0 from rfl]
        ring
      have h0 : y x₀ = 0 := by
        have := congrFun hcoc (fun _ => 1)
        rw [cochainD_of_subsingleton G (m + 1) y x₀ (fun _ => 1), hcast, one_mul] at this
        exact this
      have hyzero : y = 0 := by rw [hconst, h0]; rfl
      exact ⟨0, continuous_const, by rw [hyzero]; exact map_zero _⟩
    · -- `m` odd, so every constant cochain is a coboundary
      have hcast : ((m : ℕ) : ZMod 2) = 1 := by
        obtain ⟨k, rfl⟩ := ho
        push_cast
        rw [show ((2 : ZMod 2) * k + 1) = (2 : ZMod 2) * k + 1 from rfl,
          show (2 : ZMod 2) = 0 from rfl]
        ring
      refine ⟨fun _ => y x₀, continuous_const, ?_⟩
      funext g
      rw [cochainD_of_subsingleton G m (fun _ => y x₀) (fun _ => 1) g, hcast, one_mul]
      exact congrFun hconst.symm g
  refine ⟨fun a b => ?_⟩
  have hz : ∀ c : contCohomologyMod2 G (m + 1), c = 0 := by
    intro c
    induction c using Submodule.Quotient.induction_on with
    | H z => exact (Submodule.Quotient.mk_eq_zero _).2 (key z)
  rw [hz a, hz b]

end Cohomology

/-! ## The Milnor conjecture -/

section Statement

variable (F : Type u) [Field F]

/-- The absolute Galois group of `F`, with the Krull topology. -/
abbrev absoluteGaloisGroup : Type u := SeparableClosure F ≃ₐ[F] SeparableClosure F

/-- Mod-`2` Galois cohomology `H^n(Gal(F_sep/F), ℤ/2)`, defined with continuous cochains. -/
