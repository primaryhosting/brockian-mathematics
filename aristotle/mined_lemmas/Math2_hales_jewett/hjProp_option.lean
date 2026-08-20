import Mathlib

/-!
# Hales–Jewett: a self-contained proof

This file develops a proof of the Hales–Jewett theorem from scratch, by the *color focusing*
argument, without appealing to `Combinatorics.Line.exists_mono_in_high_dimension`.

We do reuse the (purely definitional) notion of a combinatorial line
`Combinatorics.Line` from Mathlib, together with its elementary combinators
(`map`, `prod`, `vertical`, `horizontal`, `diagonal`), but all Ramsey-theoretic content
is proved here.

The main result of this file is `Math2.hjProp_of_finite`.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

open Combinatorics

variable {α α' β κ : Type}

/-- `HJProp α κ` says that there is a finite index type `ι` such that every `κ`-coloring of the
hypercube `ι → α` admits a monochromatic combinatorial line. -/

theorem hjProp_option [Fintype β] [Nonempty β] [Finite κ]
    (ih : ∀ (κ' : Type) [Finite κ'], HJProp β κ') : HJProp (Option β) κ := by
  classical
  have hfoc : ∀ r, Focused β κ r := by
    intro r
    induction r with
    | zero => exact focused_zero
    | succ r hr => exact focused_succ ih hr
  have : Fintype κ := Fintype.ofFinite κ
  obtain ⟨ι, hι, H⟩ := hfoc (Fintype.card κ + 1)
  refine ⟨ι, hι, fun C => ?_⟩
  rcases H C with ⟨l, hl⟩ | ⟨_, colors, _, _, _, hinj⟩
  · exact ⟨l, hl⟩
  · have hcard := Fintype.card_le_of_injective colors hinj
    simp only [Fintype.card_fin] at hcard
    omega

/-- The Hales–Jewett property, by induction on the size of the alphabet. -/
