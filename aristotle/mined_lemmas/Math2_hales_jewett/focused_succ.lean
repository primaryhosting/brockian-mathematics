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

theorem focused_succ [Fintype β] [Nonempty β] [Finite κ] {r : ℕ}
    (ih : ∀ (κ' : Type) [Finite κ'], HJProp β κ') (h : Focused β κ r) : Focused β κ (r + 1) := by
  classical
  obtain ⟨ι, hι, H⟩ := h
  obtain ⟨ι', hι', H'⟩ := ih ((ι → Option β) → κ)
  refine ⟨ι ⊕ ι', inferInstance, fun C => ?_⟩
  obtain ⟨l', colorFn, hcol⟩ := H' fun y x => C (Sum.elim x fun i => some (y i))
  have hcol' : ∀ (b : β) (x : ι → Option β),
      C (Sum.elim x fun i => some (l' b i)) = colorFn x := fun b x => congrFun (hcol b) x
  have hmap : ∀ b : β, (l'.map some) (some b) = fun i => some (l' b i) := fun b =>
    Line.map_apply some l' b
  -- A monochromatic line for `colorFn` yields a monochromatic line for `C`.
  have key : ∀ l : Line (Option β) ι, l.IsMono colorFn →
      ∃ L : Line (Option β) (ι ⊕ ι'), L.IsMono C := by
    rintro l ⟨c, hc⟩
    refine ⟨l.horizontal fun i => some (l' (Classical.arbitrary β) i), c, fun a => ?_⟩
    rw [Line.horizontal_apply, hcol' (Classical.arbitrary β) (l a)]
    exact hc a
  rcases H colorFn with ⟨l, hl⟩ | ⟨lines, colors, focus, hfocus, hcolors, hinj⟩
  · exact Or.inl (key l hl)
  by_cases hex : ∃ j, colorFn focus = colors j
  · obtain ⟨j, hj⟩ := hex
    refine Or.inl (key (lines j) ⟨colors j, fun a => ?_⟩)
    cases a with
    | none => rw [hfocus j]; exact hj
    | some b => exact hcolors j b
  push_neg at hex
  refine Or.inr ⟨Fin.cases ((l'.map some).vertical focus) fun j => (lines j).prod (l'.map some),
    Fin.cases (colorFn focus) colors, Sum.elim focus ((l'.map some) none), ?_, ?_, ?_⟩
  · refine Fin.cases ?_ ?_
    · simp [Line.vertical_apply]
    · intro j
      simp [Line.prod_apply, hfocus j]
  · refine Fin.cases ?_ ?_
    · intro b
      simp only [Fin.cases_zero, Line.vertical_apply, hmap b]
      exact hcol' b focus
    · intro j b
      simp only [Fin.cases_succ, Line.prod_apply, hmap b]
      rw [hcol' b (lines j (some b))]
      exact hcolors j b
  · intro x y hxy
    induction x using Fin.cases with
    | zero =>
      induction y using Fin.cases with
      | zero => rfl
      | succ j => exact absurd (by simpa using hxy) (hex j)
    | succ i =>
      induction y using Fin.cases with
      | zero => exact absurd (by simpa using hxy.symm) (hex i)
      | succ j =>
        simp only [Fin.cases_succ] at hxy
        rw [hinj hxy]

/-- Hales–Jewett for the alphabet `Option β`, given Hales–Jewett for `β`. -/
