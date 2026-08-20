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

theorem focused_zero : Focused β κ 0 :=
  ⟨PUnit, inferInstance, fun _ =>
    Or.inr ⟨Fin.elim0, Fin.elim0, fun _ => none, fun j => j.elim0, fun j => j.elim0,
      fun a _ _ => a.elim0⟩⟩

/-- The inductive step of the color-focusing argument: assuming the Hales–Jewett property for the
alphabet `β` (with arbitrary finite color sets), a color-focused family of `r` lines can be
enlarged to one of `r + 1` lines. -/
