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

theorem hjProp_of_isEmpty [IsEmpty α] : HJProp α κ := by
  by_cases h : Nonempty κ
  · exact ⟨PUnit, inferInstance, fun _ =>
      ⟨Line.diagonal α PUnit, Classical.arbitrary κ, fun x => isEmptyElim x⟩⟩
  · exact ⟨Empty, inferInstance, fun C => absurd ⟨C fun e => e.elim⟩ h⟩

/-- `Focused β κ r` is the color-focusing statement: there is a finite index type `ι` such that
every `κ`-coloring of `ι → Option β` either has a monochromatic line, or has `r` lines with
pairwise distinct colors (the color of a line being the common color of its points indexed by
`some b`, `b : β`) which all share the same endpoint (`focus`), the point indexed by `none`. -/
