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
def HJProp (α κ : Type) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C

/-- The Hales–Jewett property only depends on the alphabet up to equivalence. -/
theorem HJProp.of_equiv (e : α ≃ α') (h : HJProp α κ) : HJProp α' κ := by
  obtain ⟨ι, hι, H⟩ := h
  refine ⟨ι, hι, fun C => ?_⟩
  obtain ⟨l, c, hc⟩ := H fun v => C (e ∘ v)
  refine ⟨l.map e, c, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [Line.map_apply]
  exact hc y

/-- Alphabets with at most one letter are trivial for Hales–Jewett. -/
theorem hjProp_of_subsingleton [Subsingleton α] [Nonempty α] : HJProp α κ := by
  refine ⟨PUnit, inferInstance, fun C => ⟨Line.diagonal α PUnit, C fun _ => Classical.arbitrary α,
    fun x => ?_⟩⟩
  rw [Line.diagonal_apply]
  congr 1
  funext _
  exact Subsingleton.elim _ _

/-- The empty alphabet is trivial for Hales–Jewett. -/
theorem hjProp_of_isEmpty [IsEmpty α] : HJProp α κ := by
  by_cases h : Nonempty κ
  · exact ⟨PUnit, inferInstance, fun _ =>
      ⟨Line.diagonal α PUnit, Classical.arbitrary κ, fun x => isEmptyElim x⟩⟩
  · exact ⟨Empty, inferInstance, fun C => absurd ⟨C fun e => e.elim⟩ h⟩

/-- `Focused β κ r` is the color-focusing statement: there is a finite index type `ι` such that
every `κ`-coloring of `ι → Option β` either has a monochromatic line, or has `r` lines with
pairwise distinct colors (the color of a line being the common color of its points indexed by
`some b`, `b : β`) which all share the same endpoint (`focus`), the point indexed by `none`. -/
def Focused (β κ : Type) (r : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → Option β) → κ,
    (∃ l : Line (Option β) ι, l.IsMono C) ∨
      ∃ (lines : Fin r → Line (Option β) ι) (colors : Fin r → κ) (focus : ι → Option β),
        (∀ j, lines j none = focus) ∧
          (∀ j (b : β), C (lines j (some b)) = colors j) ∧ Function.Injective colors

theorem focused_zero : Focused β κ 0 :=
  ⟨PUnit, inferInstance, fun _ =>
    Or.inr ⟨Fin.elim0, Fin.elim0, fun _ => none, fun j => j.elim0, fun j => j.elim0,
      fun a _ _ => a.elim0⟩⟩

/-- The inductive step of the color-focusing argument: assuming the Hales–Jewett property for the
alphabet `β` (with arbitrary finite color sets), a color-focused family of `r` lines can be
enlarged to one of `r + 1` lines. -/
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
theorem hales_jewett (α : Type) [Finite α] [Nonempty α] (κ : Type) [Finite κ] :
    ∃ n : ℕ, ∀ C : (Fin n → α) → κ,
      ∃ (S : Finset (Fin n)) (f : Fin n → α), S.Nonempty ∧
        ∀ a b : α,
          C (fun i => if i ∈ S then a else f i) = C (fun i => if i ∈ S then b else f i) := by
  classical
  obtain ⟨ι, _, hι⟩ := Math2.hjProp_of_finite α κ
  refine ⟨Fintype.card ι, fun C => ?_⟩
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  obtain ⟨l, c, hc⟩ := hι fun v => C (v ∘ e)
  refine ⟨Finset.univ.filter fun i => l.idxFun (e i) = none,
    fun i => (l.idxFun (e i)).getD (Classical.arbitrary α), ?_, ?_⟩
  · obtain ⟨j, hj⟩ := l.proper
    exact ⟨e.symm j, by simp [hj]⟩
  · have key : ∀ a : α,
        (fun i => if i ∈ Finset.univ.filter fun i => l.idxFun (e i) = none then a
          else (l.idxFun (e i)).getD (Classical.arbitrary α)) = (l a) ∘ e := by
      intro a
      funext i
      cases h : l.idxFun (e i) with
      | none => simp [h]
      | some x => simp [h]
    intro a b
    rw [key a, key b]
    exact (hc a).trans (hc b).symm

end Math2

