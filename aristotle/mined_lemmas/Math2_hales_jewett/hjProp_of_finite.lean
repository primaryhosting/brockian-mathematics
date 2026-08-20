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

theorem hjProp_of_finite (α κ : Type) [Finite α] [Finite κ] : HJProp α κ := by
  have : Fintype α := Fintype.ofFinite α
  exact hjProp_of_card (Fintype.card α) α rfl κ

end Math2

import Mathlib
import RequestProject.Core

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

/-- A *combinatorial line* in the hypercube `Fin n → α` is given by a nonempty set `S` of
"moving" coordinates together with a fixed word `f` on the remaining coordinates: its points are
`fun i => if i ∈ S then a else f i` for `a : α`.

**The Hales–Jewett theorem.** For any nonempty finite alphabet `α` and any finite set `κ` of
colors, there is a dimension `n` such that every `κ`-coloring of the hypercube `Fin n → α`
contains a monochromatic combinatorial line.

The underlying Ramsey-theoretic content is proved from scratch in `RequestProject/Core.lean`
(`Math2.hjProp_of_finite`, by the color-focusing argument); here it is transported to the
concrete hypercube `Fin n → α` with combinatorial lines described explicitly. -/
