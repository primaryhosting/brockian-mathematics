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

theorem hjProp_of_card (n : ℕ) :
    ∀ (α : Type) [Fintype α], Fintype.card α = n → ∀ (κ : Type) [Finite κ], HJProp α κ := by
  induction n with
  | zero =>
    intro α _ hcard κ _
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp hcard
    exact hjProp_of_isEmpty
  | succ n ih =>
    intro α _ hcard κ _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
      have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      exact hjProp_of_subsingleton
    · have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      have ih' : ∀ (κ' : Type) [Finite κ'], HJProp (Fin n) κ' := fun κ' _ =>
        ih (Fin n) (Fintype.card_fin n) κ'
      have hopt : HJProp (Option (Fin n)) κ := hjProp_option ih'
      exact hopt.of_equiv ((Fintype.equivFinOfCardEq hcard).trans finSuccEquivLast).symm

/-- **The Hales–Jewett theorem**, abstract form: for finite `α` and finite `κ` there is a finite
index type `ι` such that every `κ`-coloring of `ι → α` has a monochromatic combinatorial line. -/
