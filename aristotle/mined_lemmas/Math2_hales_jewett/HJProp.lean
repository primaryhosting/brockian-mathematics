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

theorem HJProp.of_equiv (e : α ≃ α') (h : HJProp α κ) : HJProp α' κ := by
  obtain ⟨ι, hι, H⟩ := h
  refine ⟨ι, hι, fun C => ?_⟩
  obtain ⟨l, c, hc⟩ := H fun v => C (e ∘ v)
  refine ⟨l.map e, c, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [Line.map_apply]
  exact hc y

/-- Alphabets with at most one letter are trivial for Hales–Jewett. -/
