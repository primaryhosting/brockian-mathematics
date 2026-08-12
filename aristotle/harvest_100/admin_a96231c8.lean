import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Existence of an Aronszajn tree

An *Aronszajn tree* is a tree of height `ω₁` all of whose levels are countable and which has no
uncountable chain (equivalently, no uncountable branch).

We construct one in the classical way, from a *coherent sequence* of finite-to-one functions
`E α : α → ℕ` (`α < ω₁`), built by transfinite recursion: `E α` is finite-to-one on `α`, and for
`β < α` the functions `E α ↾ β` and `E β` differ at only finitely many places.  The tree consists
of all pairs `(α, f)` with `α < ω₁` and `f : α → ℕ` differing from `E α` at only finitely many
places, ordered by end-extension.
-/

namespace Frontier

open Ordinal Cardinal Set

/-! ### Countability and `ω₁` -/

theorem card_lt_aleph1 {c : Cardinal.{0}} : c < ℵ_ 1 ↔ c ≤ ℵ₀ := by
  rw [show (1 : Ordinal) = Order.succ 0 by simp, aleph_succ 0, aleph_zero, Order.lt_succ_iff]

theorem lt_omega1_iff_card {α : Ordinal.{0}} : α < ω₁ ↔ α.card ≤ ℵ₀ := by
  rw [← card_lt_aleph1, ← ord_aleph 1, lt_ord]

/-- An ordinal is countable iff it is smaller than `ω₁`. -/
theorem countable_Iio_iff {α : Ordinal.{0}} : (Set.Iio α).Countable ↔ α < ω₁ := by
  rw [← Set.countable_coe_iff, ← Cardinal.mk_le_aleph0_iff, mk_Iio_ordinal, lt_omega1_iff_card,
    show (ℵ₀ : Cardinal.{1}) = Cardinal.lift.{1, 0} ℵ₀ by simp, Cardinal.lift_le]

theorem succ_lt_omega1 {α : Ordinal.{0}} (h : α < ω₁) : Order.succ α < ω₁ := by
  rw [← countable_Iio_iff] at h ⊢
  have hsub : Set.Iio (Order.succ α) ⊆ Set.Iio α ∪ {α} := by
    intro x hx
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp (Set.mem_Iio.mp hx)) with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  exact Set.Countable.mono hsub (h.union (Set.countable_singleton α))

/-! ### Ladders on countable limit ordinals -/

/-- `LadderSpec α a` says that `a : ℕ → Ordinal` is a nondecreasing sequence starting at `0`,
with all values below `α`, which is cofinal in `α`. -/
def LadderSpec (α : Ordinal.{0}) (a : ℕ → Ordinal.{0}) : Prop :=
  a 0 = 0 ∧ Monotone a ∧ (∀ n, a n < α) ∧ ∀ ξ < α, ∃ n, ξ < a n

/-- A chosen ladder on `α` (garbage unless `α` is a countable limit ordinal). -/
noncomputable def ladder (α : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if h : ∃ a, LadderSpec α a then h.choose else fun _ => 0

theorem exists_ladder {α : Ordinal.{0}} (hα : α < ω₁) (hl : Order.IsSuccLimit α) :
    ∃ a, LadderSpec α a := by
  have hpos : (0 : Ordinal) < α := hl.bot_lt
  obtain ⟨f, hf⟩ := Set.Countable.exists_surjective (s := Set.Iio α) ⟨0, hpos⟩
    (countable_Iio_iff.mpr hα)
  refine ⟨fun n => Nat.rec (0 : Ordinal.{0})
    (fun n an => max (Order.succ an) (Order.succ (f n : Ordinal.{0}))) n, rfl, ?_, ?_, ?_⟩
  · refine monotone_nat_of_le_succ (fun n => ?_)
    exact le_trans (Order.le_succ _) (le_max_left _ _)
  · intro n
    induction n with
    | zero => exact hpos
    | succ n ih => exact max_lt (hl.succ_lt ih) (hl.succ_lt (f n).2)
  · intro ξ hξ
    obtain ⟨n, hn⟩ := hf ⟨ξ, hξ⟩
    refine ⟨n + 1, ?_⟩
    have hfn : (f n : Ordinal.{0}) = ξ := congrArg Subtype.val hn
    simp only [hfn]
    exact lt_of_lt_of_le (Order.lt_succ ξ) (le_max_right _ _)

theorem ladder_spec {α : Ordinal.{0}} (hα : α < ω₁) (hl : Order.IsSuccLimit α) :
    LadderSpec α (ladder α) := by
  have h := exists_ladder hα hl
  rw [ladder, dif_pos h]
  exact h.choose_spec

/-! ### The coherent sequence -/

/-- The coherent sequence of finite-to-one functions: `E α` is a function `Ordinal → ℕ` which
vanishes outside `α`, is finite-to-one on `α`, and agrees with `E β` on `β` up to a finite set,
for every `β < α`. -/
noncomputable def E : Ordinal.{0} → Ordinal.{0} → ℕ := fun α =>
  Ordinal.limitRecOn α
    (fun _ => 0)
    (fun β eβ ξ => if ξ < β then eβ ξ else 0)
    (fun α _ ih ξ =>
      if ξ < α then
        if h : ∃ n : ℕ, ξ < ladder α (n + 1) then
          if hm : ladder α (Nat.find h + 1) < α then
            max (ih (ladder α (Nat.find h + 1)) hm ξ) (Nat.find h)
          else 0
        else 0
      else 0)

theorem E_zero (ξ : Ordinal.{0}) : E 0 ξ = 0 := by
  rw [E, Ordinal.limitRecOn_zero]

theorem E_succ (β ξ : Ordinal.{0}) : E (Order.succ β) ξ = if ξ < β then E β ξ else 0 := by
  rw [E, Ordinal.limitRecOn_succ]; rfl

theorem E_limit {α : Ordinal.{0}} (hl : Order.IsSuccLimit α) (ξ : Ordinal.{0}) :
    E α ξ =
      if ξ < α then
        if h : ∃ n : ℕ, ξ < ladder α (n + 1) then
          if _hm : ladder α (Nat.find h + 1) < α then
            max (E (ladder α (Nat.find h + 1)) ξ) (Nat.find h)
          else 0
        else 0
      else 0 := by
  conv_lhs => rw [E, Ordinal.limitRecOn_limit _ _ _ _ hl]
  rfl

theorem E_eq_zero_of_le {α ξ : Ordinal.{0}} (h : α ≤ ξ) : E α ξ = 0 := by
  revert h
  induction α using Ordinal.limitRecOn with
  | zero => intro _; exact E_zero ξ
  | succ β _ =>
      intro h
      rw [E_succ, if_neg (not_lt.mpr (le_trans (Order.le_succ β) h))]
  | limit α hl _ =>
      intro h
      rw [E_limit hl, if_neg (not_lt.mpr h)]

/-- At a countable limit ordinal, every `ξ < α` lies in a block of the ladder, and the value of
`E α` there is computed from the value of `E` at the top of that block. -/
theorem E_limit_block {α : Ordinal.{0}} (hα : α < ω₁) (hl : Order.IsSuccLimit α)
    {ξ : Ordinal.{0}} (hξ : ξ < α) :
    ∃ m : ℕ, ξ < ladder α (m + 1) ∧ (∀ j : ℕ, ξ < ladder α (j + 1) → m ≤ j) ∧
      E α ξ = max (E (ladder α (m + 1)) ξ) m := by
  obtain ⟨h0, hmono, hlt, hcof⟩ := ladder_spec hα hl
  obtain ⟨n, hn⟩ := hcof ξ hξ
  have hex : ∃ n : ℕ, ξ < ladder α (n + 1) := by
    cases n with
    | zero => rw [h0] at hn; simp at hn
    | succ n => exact ⟨n, hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min' hex hj, ?_⟩
  rw [E_limit hl, if_pos hξ, dif_pos hex, dif_pos (hlt _)]

theorem finite_of_le {γ : Ordinal.{0}} (h : ∀ k, {ξ | ξ < γ ∧ E γ ξ = k}.Finite) (k : ℕ) :
    {ξ | ξ < γ ∧ E γ ξ ≤ k}.Finite := by
  have hsub : {ξ : Ordinal.{0} | ξ < γ ∧ E γ ξ ≤ k} ⊆
      ⋃ i ∈ Set.Iic k, {ξ : Ordinal.{0} | ξ < γ ∧ E γ ξ = i} := fun ξ hξ =>
    Set.mem_biUnion (Set.mem_Iic.mpr hξ.2) ⟨hξ.1, rfl⟩
  exact Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic k) (fun i _ => h i)) hsub

/-- The two key properties of the coherent sequence, proved simultaneously by transfinite
induction: `E α` is finite-to-one on `α`, and it coheres with `E β` for every `β < α`. -/
theorem E_main (α : Ordinal.{0}) (hα : α < ω₁) :
    (∀ k, {ξ | ξ < α ∧ E α ξ = k}.Finite) ∧
      (∀ β < α, {ξ | ξ < β ∧ E α ξ ≠ E β ξ}.Finite) := by
  revert hα
  induction α using Ordinal.induction with
  | _ α ih =>
  intro hα
  rcases eq_or_ne α 0 with rfl | hα0
  · refine ⟨fun k => ?_, fun β hβ => absurd hβ (by simp)⟩
    have : {ξ : Ordinal.{0} | ξ < 0 ∧ E 0 ξ = k} = ∅ := by
      ext ξ; simp
    rw [this]
    exact Set.finite_empty
  by_cases hl : Order.IsSuccLimit α
  · -- limit case
    obtain ⟨h0, hmono, hlt, hcof⟩ := ladder_spec hα hl
    have ihl : ∀ n : ℕ, (∀ k, {ξ | ξ < ladder α (n + 1) ∧ E (ladder α (n + 1)) ξ = k}.Finite) ∧
        (∀ β < ladder α (n + 1),
          {ξ | ξ < β ∧ E (ladder α (n + 1)) ξ ≠ E β ξ}.Finite) := fun n =>
      ih _ (hlt (n + 1)) ((hlt (n + 1)).trans hα)
    constructor
    · -- finite fibers
      intro k
      have hsub : {ξ : Ordinal.{0} | ξ < α ∧ E α ξ = k} ⊆
          ⋃ j ∈ Set.Iic k,
            {ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≤ k} := by
        rintro ξ ⟨hξ, hk⟩
        obtain ⟨m, hm1, -, hm3⟩ := E_limit_block hα hl hξ
        rw [hm3] at hk
        exact Set.mem_biUnion (Set.mem_Iic.mpr (le_of_max_le_right hk.le))
          ⟨hm1, le_of_max_le_left hk.le⟩
      refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic k) (fun j _ => ?_)) hsub
      exact finite_of_le (ihl j).1 k
    · -- coherence
      intro β hβ
      obtain ⟨n, hn⟩ := hcof β hβ
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [h0] at hn
        simp at hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      set γ : Ordinal.{0} := ladder α (n + 1) with hγ
      have hγα : γ < α := hlt _
      have hγω : γ < ω₁ := hγα.trans hα
      have hstep1 : {ξ : Ordinal.{0} | ξ < γ ∧ E α ξ ≠ E γ ξ}.Finite := by
        have hsub : {ξ : Ordinal.{0} | ξ < γ ∧ E α ξ ≠ E γ ξ} ⊆
            ⋃ j ∈ Set.Iio (n + 1),
              ({ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≠ E γ ξ} ∪
                {ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≤ j}) := by
          rintro ξ ⟨hξγ, hne⟩
          have hξα : ξ < α := hξγ.trans hγα
          obtain ⟨m, hm1, hm2, hm3⟩ := E_limit_block hα hl hξα
          have hmn : m < n + 1 := Nat.lt_succ_of_le (hm2 n hξγ)
          refine Set.mem_biUnion (Set.mem_Iio.mpr hmn) ?_
          by_cases heq : E (ladder α (m + 1)) ξ = E γ ξ
          · refine Or.inr ⟨hm1, ?_⟩
            rw [hm3, heq] at hne
            omega
          · exact Or.inl ⟨hm1, heq⟩
        refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio (n + 1)) (fun j hj => ?_)) hsub
        refine Set.Finite.union ?_ (finite_of_le (ihl j).1 j)
        rcases eq_or_lt_of_le (hmono (by have := Set.mem_Iio.mp hj; omega : j + 1 ≤ n + 1)) with heq | hlt'
        · have : {ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≠ E γ ξ} = ∅ := by
            ext ξ
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
            intro _
            rw [← hγ] at heq
            rw [heq]
          rw [this]; exact Set.finite_empty
        · have hfin := ((ih γ hγα hγω).2) (ladder α (j + 1)) hlt'
          refine Set.Finite.subset hfin (fun ξ hξ => ⟨hξ.1, ?_⟩)
          exact fun hcontra => hξ.2 hcontra.symm
      have hstep2 : {ξ : Ordinal.{0} | ξ < β ∧ E γ ξ ≠ E β ξ}.Finite :=
        ((ih γ hγα hγω).2) β hn
      refine Set.Finite.subset (hstep1.union hstep2) ?_
      rintro ξ ⟨hξβ, hne⟩
      by_cases hc : E α ξ = E γ ξ
      · exact Or.inr ⟨hξβ, fun h => hne (hc.trans h)⟩
      · exact Or.inl ⟨hξβ.trans hn, hc⟩
  · -- successor case
    obtain ⟨β, rfl⟩ : ∃ β : Ordinal.{0}, α = Order.succ β := by
      rw [Order.not_isSuccLimit_iff] at hl
      rcases hl with h | h
      · exact absurd (nonpos_iff_eq_zero.mp (h (_root_.zero_le α))) hα0
      · rw [Order.not_isSuccPrelimit_iff] at h
        obtain ⟨b, -, rfl⟩ := h
        exact ⟨b, rfl⟩
    have hβα : β < Order.succ β := Order.lt_succ β
    have hβω : β < ω₁ := hβα.trans hα
    obtain ⟨ih1, ih2⟩ := ih β hβα hβω
    constructor
    · intro k
      refine Set.Finite.subset ((ih1 k).union (Set.finite_singleton β)) ?_
      rintro ξ ⟨hξ, hk⟩
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hξ) with hξ' | hξ'
      · rw [E_succ, if_pos hξ'] at hk
        exact Or.inl ⟨hξ', hk⟩
      · exact Or.inr hξ'
    · intro δ hδ
      have hmem : ∀ ξ : Ordinal.{0}, ξ < δ → E (Order.succ β) ξ = E β ξ := by
        intro ξ hξ
        rw [E_succ, if_pos (lt_of_lt_of_le hξ (Order.lt_succ_iff.mp hδ))]
      rcases eq_or_lt_of_le (Order.lt_succ_iff.mp hδ) with heq | hδβ
      · subst heq
        have : {ξ : Ordinal.{0} | ξ < δ ∧ E (Order.succ δ) ξ ≠ E δ ξ} = ∅ := by
          ext ξ
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
          exact fun hξ => hmem ξ hξ
        rw [this]; exact Set.finite_empty
      · refine Set.Finite.subset (ih2 δ hδβ) ?_
        rintro ξ ⟨hξ, hne⟩
        exact ⟨hξ, fun h => hne ((hmem ξ hξ).trans h)⟩

theorem E_finite_fibers {α : Ordinal.{0}} (hα : α < ω₁) (k : ℕ) :
    {ξ | ξ < α ∧ E α ξ = k}.Finite := (E_main α hα).1 k

theorem E_coherent {α : Ordinal.{0}} (hα : α < ω₁) {β : Ordinal.{0}} (hβ : β < α) :
    {ξ | ξ < β ∧ E α ξ ≠ E β ξ}.Finite := (E_main α hα).2 β hβ

/-! ### The tree -/

/-- A node of the Aronszajn tree: a countable ordinal `α` together with a function
`Ordinal → ℕ` supported on `α` and differing from `E α` at only finitely many places. -/
def Node : Type 1 :=
  {p : Ordinal.{0} × (Ordinal.{0} → ℕ) //
    p.1 < ω₁ ∧ (∀ ξ, p.1 ≤ ξ → p.2 ξ = 0) ∧ {ξ | ξ < p.1 ∧ p.2 ξ ≠ E p.1 ξ}.Finite}

/-- The level of a node. -/
def Node.lvl (x : Node) : Ordinal.{0} := x.1.1

/-- The function attached to a node. -/
def Node.fn (x : Node) : Ordinal.{0} → ℕ := x.1.2

theorem Node.lvl_lt_omega1 (x : Node) : x.lvl < ω₁ := x.2.1

theorem Node.fn_eq_zero (x : Node) {ξ : Ordinal.{0}} (h : x.lvl ≤ ξ) : x.fn ξ = 0 := x.2.2.1 ξ h

theorem Node.finite_diff (x : Node) : {ξ | ξ < x.lvl ∧ x.fn ξ ≠ E x.lvl ξ}.Finite := x.2.2.2

theorem Node.ext' {x y : Node} (hlvl : x.lvl = y.lvl) (hfn : x.fn = y.fn) : x = y := by
  apply Subtype.ext
  exact Prod.ext hlvl hfn

/-- The tree order: end-extension. -/
def NodeLt (x y : Node) : Prop := x.lvl < y.lvl ∧ ∀ ξ < x.lvl, x.fn ξ = y.fn ξ

theorem Node.finite_fibers (x : Node) (k : ℕ) : {ξ | ξ < x.lvl ∧ x.fn ξ = k}.Finite := by
  refine Set.Finite.subset (x.finite_diff.union (E_finite_fibers x.lvl_lt_omega1 k)) ?_
  rintro ξ ⟨hξ, hk⟩
  by_cases hd : x.fn ξ = E x.lvl ξ
  · exact Or.inr ⟨hξ, hd ▸ hk⟩
  · exact Or.inl ⟨hξ, hd⟩

/-- Restriction of a node to a smaller level. -/
noncomputable def Node.restrict (x : Node) {β : Ordinal.{0}} (hβ : β < x.lvl) : Node :=
  ⟨(β, fun ξ => if ξ < β then x.fn ξ else 0),
    hβ.trans x.lvl_lt_omega1,
    fun ξ h => if_neg (not_lt.mpr h),
    by
      refine Set.Finite.subset
        (x.finite_diff.union (E_coherent x.lvl_lt_omega1 hβ)) ?_
      rintro ξ ⟨hξ, hne⟩
      dsimp only at hξ hne
      rw [if_pos hξ] at hne
      by_cases hd : x.fn ξ = E x.lvl ξ
      · exact Or.inr ⟨hξ, fun h => hne (hd.trans h)⟩
      · exact Or.inl ⟨hξ.trans hβ, hd⟩⟩

theorem Node.restrict_lvl (x : Node) {β : Ordinal.{0}} (hβ : β < x.lvl) :
    (x.restrict hβ).lvl = β := rfl

theorem Node.restrict_fn (x : Node) {β : Ordinal.{0}} (hβ : β < x.lvl) {ξ : Ordinal.{0}}
    (hξ : ξ < β) : (x.restrict hβ).fn ξ = x.fn ξ := if_pos hξ

/-- The canonical node of level `α`, given by the coherent sequence itself. -/
noncomputable def Node.base (α : Ordinal.{0}) (hα : α < ω₁) : Node :=
  ⟨(α, E α), hα, fun _ h => E_eq_zero_of_le h, by
    have : {ξ : Ordinal.{0} | ξ < α ∧ E α ξ ≠ E α ξ} = ∅ := by
      ext ξ; simp
    rw [this]; exact Set.finite_empty⟩

theorem Node.base_lvl (α : Ordinal.{0}) (hα : α < ω₁) : (Node.base α hα).lvl = α := rfl

/-! ### Aronszajn trees -/

/-- `IsAronszajnTree lt lvl` states that the strict order `lt` on `T`, whose level function is
`lvl`, is an Aronszajn tree: it is a tree (the predecessors of a node are linearly ordered, and
`lvl` maps them bijectively onto the ordinals below `lvl x`) of height `ω₁` whose levels are all
countable and which has no uncountable chain. -/
structure IsAronszajnTree {T : Type*} (lt : T → T → Prop) (lvl : T → Ordinal.{0}) : Prop where
  /-- `lt` is transitive. -/
  trans : ∀ x y z, lt x y → lt y z → lt x z
  /-- `lt` is irreflexive. -/
  irrefl : ∀ x, ¬ lt x x
  /-- The level function is strictly monotone. -/
  lvl_lt : ∀ x y, lt x y → lvl x < lvl y
  /-- The predecessors of a node are linearly ordered. -/
  pred_linear : ∀ x y z, lt y x → lt z x → lt y z ∨ y = z ∨ lt z y
  /-- Each node has exactly one predecessor of each smaller level. -/
  pred_unique : ∀ x, ∀ β < lvl x, ∃! y, lt y x ∧ lvl y = β
  /-- All levels are below `ω₁`. -/
  lvl_lt_omega1 : ∀ x, lvl x < ω₁
  /-- The tree has height `ω₁`: every level below `ω₁` is nonempty. -/
  levels_nonempty : ∀ α < ω₁, ∃ x, lvl x = α
  /-- Every level is countable. -/
  levels_countable : ∀ α, {x | lvl x = α}.Countable
  /-- There is no uncountable chain. -/
  chain_countable : ∀ C : Set T, IsChain lt C → C.Countable

theorem levels_countable_aux (α : Ordinal.{0}) : {x : Node | x.lvl = α}.Countable := by
  by_cases hα : α < ω₁
  · set g : Node → Set (Ordinal.{0} × ℕ) :=
      fun x => (fun ξ => (ξ, x.fn ξ)) '' {ξ | ξ < x.lvl ∧ x.fn ξ ≠ E x.lvl ξ} with hg
    have key : ∀ x ∈ {x : Node | x.lvl = α}, ∀ y ∈ {x : Node | x.lvl = α}, g x = g y →
        ∀ ξ : Ordinal.{0}, ξ < α → x.fn ξ ≠ E α ξ → y.fn ξ = x.fn ξ := by
      intro x hx y hy hxy ξ hξ hne
      have hmem : (ξ, x.fn ξ) ∈ g x := ⟨ξ, ⟨by rw [hx]; exact hξ, by rw [hx]; exact hne⟩, rfl⟩
      rw [hxy] at hmem
      obtain ⟨η, -, hη⟩ := hmem
      have h1 : η = ξ := congrArg Prod.fst hη
      have h2 : y.fn η = x.fn ξ := congrArg Prod.snd hη
      rwa [h1] at h2
    refine Set.countable_of_injective_of_countable_image (f := g) ?_ ?_
    · intro x hx y hy hxy
      refine Node.ext' (by rw [hx, hy] : x.lvl = y.lvl) (funext fun ξ => ?_)
      by_cases hξ : ξ < α
      · by_cases hdx : x.fn ξ = E α ξ
        · by_cases hdy : y.fn ξ = E α ξ
          · rw [hdx, hdy]
          · exact key y hy x hx hxy.symm ξ hξ hdy
        · exact (key x hx y hy hxy ξ hξ hdx).symm
      · rw [x.fn_eq_zero (by rw [hx]; exact not_lt.mp hξ),
          y.fn_eq_zero (by rw [hy]; exact not_lt.mp hξ)]
    · have hcount : ((Set.Iio α) ×ˢ (Set.univ : Set ℕ)).Countable :=
        Set.Countable.prod (countable_Iio_iff.mpr hα) Set.countable_univ
      refine Set.Countable.mono ?_ (Set.countable_setOf_finite_subset hcount)
      rintro t ⟨x, hx, rfl⟩
      refine ⟨Set.Finite.image _ x.finite_diff, ?_⟩
      rintro p ⟨ξ, hξ, rfl⟩
      exact ⟨show ξ ∈ Set.Iio α from hx ▸ hξ.1, Set.mem_univ _⟩
  · have hempty : {x : Node | x.lvl = α} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hα (h ▸ x.lvl_lt_omega1)
    rw [hempty]
    exact Set.countable_empty

theorem chain_countable_aux (C : Set Node) (hC : IsChain NodeLt C) : C.Countable := by
  by_contra hcount
  have hagree : ∀ x ∈ C, ∀ y ∈ C, ∀ ξ : Ordinal.{0}, ξ < x.lvl → ξ < y.lvl → x.fn ξ = y.fn ξ := by
    intro x hx y hy ξ hξx hξy
    rcases eq_or_ne x y with rfl | hne
    · rfl
    · rcases hC hx hy hne with h | h
      · exact h.2 ξ hξx
      · exact (h.2 ξ hξy).symm
  have hinj : Set.InjOn Node.lvl C := by
    intro x hx y hy hxy
    by_contra hne
    rcases hC hx hy hne with h | h
    · exact absurd hxy (ne_of_lt h.1)
    · exact absurd hxy.symm (ne_of_lt h.1)
  have hAunc : ¬ (Node.lvl '' C).Countable := fun h =>
    hcount (Set.countable_of_injective_of_countable_image hinj h)
  have habove : ∀ x ∈ C, ∃ y ∈ C, x.lvl < y.lvl := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    refine hAunc (Set.Countable.mono ?_ (countable_Iio_iff.mpr (succ_lt_omega1 x.lvl_lt_omega1)))
    rintro β ⟨y, hy, rfl⟩
    exact Set.mem_Iio.mpr (Order.lt_succ_iff.mpr (hcon y hy))
  set D : Set Ordinal.{0} := {ξ | ∃ x ∈ C, ξ < x.lvl} with hD
  set F : Ordinal.{0} → ℕ :=
    fun ξ => if h : ∃ x, x ∈ C ∧ ξ < x.lvl then h.choose.fn ξ else 0 with hF
  have hFval : ∀ x ∈ C, ∀ ξ : Ordinal.{0}, ξ < x.lvl → F ξ = x.fn ξ := by
    intro x hx ξ hξ
    have hex : ∃ y, y ∈ C ∧ ξ < y.lvl := ⟨x, hx, hξ⟩
    rw [hF]
    simp only [dif_pos hex]
    exact hagree _ hex.choose_spec.1 x hx ξ hex.choose_spec.2 hξ
  have hDunc : ¬ D.Countable := by
    intro h
    refine hAunc (Set.Countable.mono ?_ h)
    rintro β ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := habove x hx
    exact ⟨y, hy, hxy⟩
  have hfin : ∀ (k : ℕ), ∀ ξ ∈ D, {η : Ordinal.{0} | (η ∈ D ∧ F η = k) ∧ η < ξ}.Finite := by
    intro k ξ hξ
    obtain ⟨x, hx, hξx⟩ := hξ
    refine Set.Finite.subset (x.finite_fibers k) ?_
    rintro η ⟨⟨-, hFη⟩, hηξ⟩
    have hηx : η < x.lvl := hηξ.trans hξx
    exact ⟨hηx, by rw [← hFval x hx η hηx]; exact hFη⟩
  have hScount : ∀ k : ℕ, {η : Ordinal.{0} | η ∈ D ∧ F η = k}.Countable := by
    intro k
    rw [Set.countable_iff_exists_injOn]
    refine ⟨fun η => {μ : Ordinal.{0} | (μ ∈ D ∧ F μ = k) ∧ μ < η}.ncard, ?_⟩
    have hmono : ∀ η ∈ {η : Ordinal.{0} | η ∈ D ∧ F η = k},
        ∀ η' ∈ {η : Ordinal.{0} | η ∈ D ∧ F η = k}, η < η' →
          {μ : Ordinal.{0} | (μ ∈ D ∧ F μ = k) ∧ μ < η}.ncard <
            {μ : Ordinal.{0} | (μ ∈ D ∧ F μ = k) ∧ μ < η'}.ncard := by
      intro η hη η' hη' hlt
      refine Set.ncard_lt_ncard ⟨fun μ hμ => ⟨hμ.1, hμ.2.trans hlt⟩, ?_⟩ (hfin k η' hη'.1)
      intro hsub
      exact absurd (hsub ⟨hη, hlt⟩).2 (lt_irrefl η)
    intro η hη η' hη' heq
    rcases lt_trichotomy η η' with h | h | h
    · exact absurd heq (ne_of_lt (hmono η hη η' hη' h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hmono η' hη' η hη h))
  refine hDunc (Set.Countable.mono ?_ (Set.countable_iUnion hScount))
  intro ξ hξ
  exact Set.mem_iUnion.mpr ⟨F ξ, hξ, rfl⟩

/-- **There exists an Aronszajn tree**: a tree of height `ω₁` all of whose levels are countable
and which has no uncountable chain. -/
theorem Aronszajn_tree_exists :
    ∃ (T : Type 1) (lt : T → T → Prop) (lvl : T → Ordinal.{0}), IsAronszajnTree lt lvl := by
  refine ⟨Node, NodeLt, Node.lvl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, levels_countable_aux, chain_countable_aux⟩
  · rintro x y z ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨h1.trans h3, fun ξ hξ => (h2 ξ hξ).trans (h4 ξ (hξ.trans h1))⟩
  · exact fun x h => lt_irrefl _ h.1
  · exact fun _ _ h => h.1
  · rintro x y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
    rcases lt_trichotomy y.lvl z.lvl with h | h | h
    · exact Or.inl ⟨h, fun ξ hξ => (hy2 ξ hξ).trans (hz2 ξ (hξ.trans h)).symm⟩
    · refine Or.inr (Or.inl (Node.ext' h (funext fun ξ => ?_)))
      by_cases hξ : ξ < y.lvl
      · exact (hy2 ξ hξ).trans (hz2 ξ (h ▸ hξ)).symm
      · rw [y.fn_eq_zero (not_lt.mp hξ), z.fn_eq_zero (h ▸ not_lt.mp hξ)]
    · exact Or.inr (Or.inr ⟨h, fun ξ hξ => (hz2 ξ hξ).trans (hy2 ξ (hξ.trans h)).symm⟩)
  · intro x β hβ
    refine ⟨x.restrict hβ, ⟨⟨?_, ?_⟩, x.restrict_lvl hβ⟩, ?_⟩
    · rw [x.restrict_lvl hβ]; exact hβ
    · intro ξ hξ
      rw [x.restrict_lvl hβ] at hξ
      exact x.restrict_fn hβ hξ
    · rintro y ⟨⟨-, hy⟩, hylvl⟩
      refine Node.ext' (by rw [hylvl, x.restrict_lvl hβ]) (funext fun ξ => ?_)
      by_cases hξ : ξ < β
      · rw [x.restrict_fn hβ hξ]
        exact hy ξ (by rw [hylvl]; exact hξ)
      · rw [y.fn_eq_zero (by rw [hylvl]; exact not_lt.mp hξ),
          (x.restrict hβ).fn_eq_zero (by rw [x.restrict_lvl hβ]; exact not_lt.mp hξ)]
  · exact fun x => x.lvl_lt_omega1
  · exact fun α hα => ⟨Node.base α hα, rfl⟩

end Frontier

