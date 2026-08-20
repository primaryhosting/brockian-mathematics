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

def Focused (β κ : Type) (r : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → Option β) → κ,
    (∃ l : Line (Option β) ι, l.IsMono C) ∨
      ∃ (lines : Fin r → Line (Option β) ι) (colors : Fin r → κ) (focus : ι → Option β),
        (∀ j, lines j none = focus) ∧
          (∀ j (b : β), C (lines j (some b)) = colors j) ∧ Function.Injective colors

