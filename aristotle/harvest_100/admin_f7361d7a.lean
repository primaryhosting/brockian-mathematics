import Mathlib

/-!
# The cumulative hierarchy and inaccessible cardinals

This file defines the von Neumann cumulative hierarchy `Frontier.cumul o` inside `ZFSet`,
characterizes its members by rank, and proves the two facts about an inaccessible cardinal `κ`
that are needed to see that `V_κ` is a model of ZFC:

* `Frontier.card_lt_of_rank_lt`: a set of rank `< κ.ord` has cardinality `< κ`;
* `Frontier.rank_range_lt`: `V_κ` is closed under images of small families (replacement).
-/

open Ordinal Cardinal

namespace Frontier

/-- The von Neumann cumulative hierarchy `V_o`, as a `ZFSet`. -/
noncomputable def cumul (o : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.iUnion (fun i : o.ToType => ZFSet.powerset (cumul ((typein (α := o.ToType) (· < ·)) i)))
termination_by o
decreasing_by exact typein_lt_self i

theorem cumul_def (o : Ordinal.{u}) : cumul o =
    ZFSet.iUnion
      (fun i : o.ToType => ZFSet.powerset (cumul ((typein (α := o.ToType) (· < ·)) i))) := by
  rw [cumul]

/-- The members of `V_o` are exactly the sets of rank `< o`. -/
theorem mem_cumul {o : Ordinal.{u}} {x : ZFSet.{u}} : x ∈ cumul o ↔ x.rank < o := by
  induction o using Ordinal.induction generalizing x with
  | h o ih =>
    rw [cumul_def, ZFSet.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rw [ZFSet.mem_powerset] at hi
      have hle : x.rank ≤ typein (α := o.ToType) (· < ·) i := by
        rw [ZFSet.rank_le_iff]
        intro y hy
        exact (ih _ (typein_lt_self i)).1 (hi hy)
      exact lt_of_le_of_lt hle (typein_lt_self i)
    · intro h
      refine ⟨(enum (α := o.ToType) (· < ·)) ⟨x.rank, by rwa [type_toType]⟩, ?_⟩
      rw [ZFSet.mem_powerset]
      intro y hy
      have he : typein (α := o.ToType) (· < ·)
          ((enum (α := o.ToType) (· < ·)) ⟨x.rank, by rwa [type_toType]⟩) = x.rank :=
        typein_enum _ _
      rw [he, ih _ h]
      exact ZFSet.rank_lt_of_mem hy

theorem rank_cumul_le (o : Ordinal.{u}) : (cumul o).rank ≤ o := by
  rw [ZFSet.rank_le_iff]
  intro y hy
  exact mem_cumul.1 hy

/-- Every set of rank `< o` is a subset of `V_o`. -/
theorem subset_cumul {x : ZFSet.{u}} : x ⊆ cumul x.rank := fun _ hy =>
  mem_cumul.2 (ZFSet.rank_lt_of_mem hy)

variable {κ : Cardinal.{u}}

/-- If `κ` is inaccessible then every level of the cumulative hierarchy below `κ` has
cardinality less than `κ`. -/
theorem card_cumul_lt (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → (cumul o).card < κ := by
  intro o
  induction o using Ordinal.induction with
  | h o ih =>
    intro ho
    rw [cumul_def]
    have h1 : Cardinal.lift.{u, u} (ZFSet.iUnion (fun i : o.ToType =>
        ZFSet.powerset (cumul ((typein (α := o.ToType) (· < ·)) i)))).card
        ≤ sum (fun i : o.ToType =>
            (ZFSet.powerset (cumul ((typein (α := o.ToType) (· < ·)) i))).card) :=
      ZFSet.lift_card_iUnion_le_sum_card
    rw [Cardinal.lift_id] at h1
    refine lt_of_le_of_lt h1 (sum_lt_of_isRegular hκ.isRegular ?_ ?_)
    · rw [mk_toType]
      exact Cardinal.lt_ord.1 ho
    · intro i
      rw [ZFSet.card_powerset]
      exact hκ.isStrongLimit.two_power_lt
        (ih _ (typein_lt_self i) ((typein_lt_self i).trans ho))

/-- A set of rank below `κ.ord` has fewer than `κ` elements. -/
theorem card_lt_of_rank_lt (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x.rank < κ.ord) :
    x.card < κ :=
  lt_of_le_of_lt (ZFSet.card_mono subset_cumul) (card_cumul_lt hκ _ hx)

/-- `κ.ord` is a limit ordinal. -/
theorem isSuccLimit_ord (hκ : κ.IsInaccessible) : Order.IsSuccLimit κ.ord :=
  Cardinal.isSuccLimit_ord hκ.isRegular.aleph0_le

/-- Replacement: the range of a family of sets of rank `< κ.ord` indexed by a type of size
`< κ` again has rank `< κ.ord`. -/
theorem rank_range_lt (hκ : κ.IsInaccessible) {ι : Type u} (f : ι → ZFSet.{u})
    (hι : #ι < κ) (hf : ∀ i, (f i).rank < κ.ord) : (ZFSet.range f).rank < κ.ord := by
  rw [ZFSet.rank_range]
  refine Ordinal.iSup_lt_ord ?_ fun i => (isSuccLimit_ord hκ).succ_lt (hf i)
  rwa [hκ.isRegular.cof_eq]

end Frontier

import Mathlib
import RequestProject.SetLanguage
import RequestProject.Cumulative

/-!
# `V_κ` is a model of ZFC for `κ` inaccessible

For an inaccessible cardinal `κ` we equip the collection `VSet κ` of all sets of rank `< κ.ord`
with the structure of a first-order structure in the language of set theory and verify each
axiom of `Frontier.ZFC` in it.
-/

open FirstOrder Language Cardinal Ordinal

namespace Frontier

variable {κ : Cardinal.{u}}

/-- The `κ`-th level of the cumulative hierarchy, as a type: all sets of rank `< κ.ord`. -/
abbrev VSet (κ : Cardinal.{u}) : Type (u + 1) := {x : ZFSet.{u} // x.rank < κ.ord}

instance vsetStructure : setLang.Structure (VSet κ) where
  funMap f := Empty.elim f
  RelMap {n} r x := match n, r with
    | 2, memRel.mem => (x 0).1 ∈ (x 1).1

theorem memM_iff {x y : VSet κ} : memM x y ↔ x.1 ∈ y.1 := Iff.rfl

/-- Membership in an element of `V_κ` stays inside `V_κ`. -/
theorem rank_lt_of_mem_val {x : VSet κ} {z : ZFSet.{u}} (hz : z ∈ x.1) : z.rank < κ.ord :=
  (ZFSet.rank_lt_of_mem hz).trans x.2

/-- The element of `V_κ` determined by a member of an element of `V_κ`. -/
def VSet.mk' {x : VSet κ} {z : ZFSet.{u}} (hz : z ∈ x.1) : VSet κ := ⟨z, rank_lt_of_mem_val hz⟩

theorem rank_le_of_subset {x y : ZFSet.{u}} (h : x ⊆ y) : x.rank ≤ y.rank :=
  ZFSet.rank_le_iff.2 fun _ hz => ZFSet.rank_lt_of_mem (h hz)

theorem ord_pos (hκ : κ.IsInaccessible) : 0 < κ.ord :=
  Cardinal.lt_ord.2 (by simpa using hκ.pos)

theorem nonempty_VSet (hκ : κ.IsInaccessible) : Nonempty (VSet κ) :=
  ⟨⟨∅, by simpa using ord_pos hκ⟩⟩

/-! ### Verification of the axioms -/

theorem VSet.models_axExt : (VSet κ) ⊨ axExt := by
  rw [realize_axExt]
  intro x y h
  refine Subtype.ext (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · exact (h ⟨z, rank_lt_of_mem_val hz⟩).1 hz
  · exact (h ⟨z, rank_lt_of_mem_val hz⟩).2 hz

theorem VSet.models_axPair (hκ : κ.IsInaccessible) : (VSet κ) ⊨ axPair := by
  rw [realize_axPair]
  intro x y
  refine ⟨⟨{x.1, y.1}, ?_⟩, ?_⟩
  · rw [ZFSet.rank_pair]
    exact max_lt ((isSuccLimit_ord hκ).succ_lt x.2) ((isSuccLimit_ord hκ).succ_lt y.2)
  · intro z
    show z.1 ∈ ({x.1, y.1} : ZFSet) ↔ _
    rw [ZFSet.mem_pair]
    exact or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm

theorem VSet.models_axUnion : (VSet κ) ⊨ axUnion := by
  rw [realize_axUnion]
  intro a
  refine ⟨⟨ZFSet.sUnion a.1, lt_of_le_of_lt (ZFSet.rank_sUnion_le a.1) a.2⟩, fun z => ?_⟩
  show z.1 ∈ ZFSet.sUnion a.1 ↔ _
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hzy⟩
    exact ⟨⟨y, rank_lt_of_mem_val hy⟩, hy, hzy⟩
  · rintro ⟨y, hy, hzy⟩
    exact ⟨y.1, hy, hzy⟩

theorem VSet.models_axPow (hκ : κ.IsInaccessible) : (VSet κ) ⊨ axPow := by
  rw [realize_axPow]
  intro a
  refine ⟨⟨ZFSet.powerset a.1, ?_⟩, fun z => ?_⟩
  · rw [ZFSet.rank_powerset]
    exact (isSuccLimit_ord hκ).succ_lt a.2
  · show z.1 ∈ ZFSet.powerset a.1 ↔ _
    rw [ZFSet.mem_powerset]
    constructor
    · intro h w hw
      exact h hw
    · intro h w hw
      exact h ⟨w, rank_lt_of_mem_val hw⟩ hw

theorem VSet.models_axInf (hκ : κ.IsInaccessible) : (VSet κ) ⊨ axInf := by
  rw [realize_axInf]
  have homega : (Ordinal.omega0 : Ordinal.{u}) < κ.ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.2 hκ.aleph0_lt
  have hempty : (∅ : ZFSet.{u}).rank < κ.ord := by simpa using ord_pos hκ
  refine ⟨⟨cumul Ordinal.omega0, lt_of_le_of_lt (rank_cumul_le _) homega⟩,
    ⟨⟨⟨∅, hempty⟩, ?_, ?_⟩, ?_⟩⟩
  · show (∅ : ZFSet) ∈ cumul Ordinal.omega0
    exact mem_cumul.2 (by simp)
  · intro z hz
    exact ZFSet.notMem_empty _ hz
  · intro x hx
    have hrx : x.1.rank < Ordinal.omega0 := mem_cumul.1 hx
    have hins : (insert x.1 x.1 : ZFSet).rank < Ordinal.omega0 := by
      rw [ZFSet.rank_insert]
      exact max_lt (Order.IsSuccLimit.succ_lt Ordinal.isSuccLimit_omega0 hrx) hrx
    refine ⟨⟨insert x.1 x.1, hins.trans homega⟩, ?_, fun z => ?_⟩
    · show insert x.1 x.1 ∈ cumul Ordinal.omega0
      exact mem_cumul.2 hins
    · show z.1 ∈ insert x.1 x.1 ↔ _
      rw [ZFSet.mem_insert_iff]
      constructor
      · rintro (h | h)
        · exact Or.inr (Subtype.ext h)
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (congrArg Subtype.val h)

theorem VSet.models_axFound : (VSet κ) ⊨ axFound := by
  rw [realize_axFound]
  rintro a ⟨x, hx⟩
  have hxa : x.1 ∈ a.1 := hx
  have hne : a.1 ≠ ∅ := fun h => ZFSet.notMem_empty x.1 (h ▸ hxa)
  obtain ⟨y, hy, hinter⟩ := ZFSet.regularity a.1 hne
  refine ⟨⟨y, rank_lt_of_mem_val hy⟩, hy, fun w hw hwa => ?_⟩
  have hmem : w.1 ∈ a.1 ∩ y := ZFSet.mem_inter.2 ⟨hwa, hw⟩
  rw [hinter] at hmem
  exact ZFSet.notMem_empty _ hmem

open Classical in
theorem VSet.models_axChoice : (VSet κ) ⊨ axChoice := by
  rw [realize_axChoice]
  rintro a ⟨hne, hdisj⟩
  -- a choice function on the members of `a`
  set pick : ZFSet.{u} → ZFSet.{u} := fun x => if h : ∃ z, z ∈ x then h.choose else ∅ with hpick
  have hpick_mem : ∀ x : ZFSet.{u}, x ∈ a.1 → pick x ∈ x := by
    intro x hx
    have hx' : ∃ z, z ∈ x := by
      obtain ⟨z, hz⟩ := hne ⟨x, rank_lt_of_mem_val hx⟩ hx
      exact ⟨z.1, hz⟩
    rw [hpick]
    simp only [dif_pos hx']
    exact hx'.choose_spec
  refine ⟨⟨ZFSet.sep (fun z => ∃ x ∈ a.1, pick x = z) (ZFSet.sUnion a.1), ?_⟩, fun x hx => ?_⟩
  · exact lt_of_le_of_lt (le_trans (rank_le_of_subset fun z hz => (ZFSet.mem_sep.1 hz).1)
      (ZFSet.rank_sUnion_le a.1)) a.2
  · have hpx : pick x.1 ∈ x.1 := hpick_mem x.1 hx
    refine ⟨⟨pick x.1, rank_lt_of_mem_val hpx⟩, ⟨hpx, ?_⟩, fun w hw => ?_⟩
    · show pick x.1 ∈ ZFSet.sep (fun z => ∃ x ∈ a.1, pick x = z) (ZFSet.sUnion a.1)
      rw [ZFSet.mem_sep]
      exact ⟨ZFSet.mem_sUnion.2 ⟨x.1, hx, hpx⟩, ⟨x.1, hx, rfl⟩⟩
    · obtain ⟨hwx, hwc⟩ := hw
      have hwc' : w.1 ∈ ZFSet.sep (fun z => ∃ x ∈ a.1, pick x = z) (ZFSet.sUnion a.1) := hwc
      obtain ⟨-, x', hx', hpx'⟩ := ZFSet.mem_sep.1 hwc'
      have hx'eq : x' = x.1 := by
        by_contra hne'
        have hmem : w.1 ∈ x' := hpx' ▸ hpick_mem x' hx'
        exact hdisj ⟨x', rank_lt_of_mem_val hx'⟩ x
          ⟨⟨hx', hx⟩, fun hc => hne' (congrArg Subtype.val hc)⟩ w hmem hwx
      exact Subtype.ext (by rw [← hpx', hx'eq])

open Classical in
theorem VSet.models_axSep (n : ℕ) (φ : setLang.Formula (Fin n ⊕ Unit)) :
    (VSet κ) ⊨ axSep n φ := by
  rw [realize_axSep]
  intro p a
  set P : ZFSet.{u} → Prop :=
    fun z => ∃ h : z.rank < κ.ord, φ.Realize (Sum.elim p (fun _ => (⟨z, h⟩ : VSet κ)))
  refine ⟨⟨ZFSet.sep P a.1,
      lt_of_le_of_lt (rank_le_of_subset fun z hz => (ZFSet.mem_sep.1 hz).1) a.2⟩, fun x => ?_⟩
  show x.1 ∈ ZFSet.sep P a.1 ↔ _
  rw [ZFSet.mem_sep]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨h, hφ⟩
    exact hφ
  · intro hφ
    exact ⟨x.2, hφ⟩

open Classical in
theorem VSet.models_axRep (hκ : κ.IsInaccessible) (n : ℕ)
    (φ : setLang.Formula (Fin n ⊕ Bool)) : (VSet κ) ⊨ axRep n φ := by
  rw [realize_axRep]
  intro p a hfun
  set R : VSet κ → VSet κ → Prop :=
    fun x y => φ.Realize (Sum.elim p (fun c => cond c y x))
  -- index the elements of `a` by a type in the right universe
  set ι₀ : Type u := Shrink.{u} ↥(a.1)
  set elt : ι₀ → VSet κ := fun i =>
    ⟨((equivShrink ↥(a.1)).symm i).1, rank_lt_of_mem_val ((equivShrink ↥(a.1)).symm i).2⟩
  have helt_mem : ∀ i, (elt i).1 ∈ a.1 := fun i => ((equivShrink ↥(a.1)).symm i).2
  set ι : Type u := {i : ι₀ // ∃ y : VSet κ, R (elt i) y}
  set f : ι → ZFSet.{u} := fun i => (Classical.choose i.2).1
  have hfspec : ∀ i : ι, R (elt i.1) (Classical.choose i.2) := fun i => Classical.choose_spec i.2
  refine ⟨⟨ZFSet.range f, rank_range_lt hκ f ?_ fun i => (Classical.choose i.2).2⟩, fun y => ?_⟩
  · refine lt_of_le_of_lt (Cardinal.mk_subtype_le _) ?_
    have : #ι₀ = a.1.card := rfl
    rw [this]
    exact card_lt_of_rank_lt hκ a.2
  · show y.1 ∈ ZFSet.range f ↔ _
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨elt i.1, helt_mem i.1, ?_⟩
      have : Classical.choose i.2 = y := Subtype.ext hi
      rw [← this]
      exact hfspec i
    · rintro ⟨x, hx, hxy⟩
      have hx' : x.1 ∈ a.1 := hx
      set i₀ : ι₀ := equivShrink ↥(a.1) ⟨x.1, hx'⟩
      have helti : elt i₀ = x := by
        refine Subtype.ext ?_
        show ((equivShrink ↥(a.1)).symm (equivShrink ↥(a.1) ⟨x.1, hx'⟩)).1 = x.1
        rw [Equiv.symm_apply_apply]
      have hex : ∃ z : VSet κ, R (elt i₀) z := ⟨y, by rw [helti]; exact hxy⟩
      refine ⟨⟨i₀, hex⟩, ?_⟩
      have hspec : R x (Classical.choose hex) := by
        rw [← helti]
        exact Classical.choose_spec hex
      have : Classical.choose hex = y := hfun x (Classical.choose hex) y ⟨⟨hx, hspec⟩, hxy⟩
      show (Classical.choose hex).1 = y.1
      rw [this]

/-- **`V_κ` is a model of ZFC** whenever `κ` is inaccessible. -/
theorem VSet.models_ZFC (hκ : κ.IsInaccessible) : (VSet κ) ⊨ ZFC := by
  haveI := nonempty_VSet hκ
  rw [models_ZFC_iff]
  exact ⟨⟨VSet.models_axExt, VSet.models_axPair hκ, VSet.models_axUnion,
    VSet.models_axPow hκ, VSet.models_axInf hκ, VSet.models_axFound, VSet.models_axChoice⟩,
    fun n φ => VSet.models_axSep n φ, fun n φ => VSet.models_axRep hκ n φ⟩

end Frontier

import Mathlib
import RequestProject.SetLanguage
import RequestProject.Cumulative
import RequestProject.Model

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized

`Frontier.ZFC` is the theory of ZFC, written in the first-order language
`Frontier.setLang` with a single binary relation symbol (see `RequestProject/SetLanguage.lean`):
extensionality, pairing, union, power set, infinity, foundation and choice, together with the
full separation and replacement schemes (one axiom for every formula with parameters).
Each axiom comes with a lemma computing its meaning in an arbitrary structure, so the
formalization can be checked against the usual informal statements.

For a cardinal `κ`, `Frontier.VSet κ` is the collection of all sets (`ZFSet`) of rank `< κ.ord`,
i.e. the level `V_κ` of the cumulative hierarchy, viewed as a structure for `setLang`.
The main result is that `V_κ` is a model of ZFC whenever `κ` is inaccessible, so that the
existence of an inaccessible cardinal implies the consistency of ZFC.

Since Mathlib's model theory provides semantics but no deductive calculus, consistency is
expressed as satisfiability, `FirstOrder.Language.Theory.IsSatisfiable` (the two are equivalent
by Gödel's completeness theorem). The reduction `Con(ZFC + inaccessible) → Con(ZFC)` in this
setting is the monotonicity statement `Frontier.ConZFC_of_extension`.

A remark on strength: the mathematical content of the development is the construction of the
model, `Frontier.VSet.models_ZFC`, which says that `V_κ ⊨ ZFC` for `κ` inaccessible. The
consequence `Frontier.ZFC.IsSatisfiable` is stated under the hypothesis that an inaccessible
cardinal exists, as in the informal statement; note that Lean's own type-theoretic foundation is
itself strong enough to prove Con(ZFC), so no formalization of Con(ZFC) inside Lean can be
independent of that ambient strength.

As a check that the axiomatization is not degenerate,
`Frontier.no_universal_set_of_models_ZFC` derives Russell's paradox from an instance of the
separation scheme in an arbitrary model.
-/

open FirstOrder Language Cardinal

namespace Frontier

/-- **An inaccessible cardinal yields a model of ZFC.**

If `κ` is an inaccessible cardinal, then the level `V_κ` of the cumulative hierarchy is a model
of ZFC; consequently ZFC is satisfiable (consistent). -/
theorem inaccessible_implies_ConZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    (VSet κ) ⊨ ZFC ∧ ZFC.IsSatisfiable := by
  haveI := nonempty_VSet hκ
  haveI := VSet.models_ZFC hκ
  exact ⟨VSet.models_ZFC hκ, Theory.Model.isSatisfiable (VSet κ)⟩

/-- A sanity check on the formalization: in any model of `Frontier.ZFC` there is no universal
set. (This uses the instance of the separation scheme given by the formula `¬ x ∈ x`, and rules
out degenerate models.) -/
theorem no_universal_set_of_models_ZFC {M : Type*} [setLang.Structure M] (h : M ⊨ ZFC) :
    ¬ ∃ u : M, ∀ x : M, memM x u := by
  rintro ⟨u, hu⟩
  have hsep := (models_ZFC_iff.1 h).2.1 0
    (Formula.not (memF (Term.var (Sum.inr ())) (Term.var (Sum.inr ()))))
  rw [realize_axSep] at hsep
  obtain ⟨b, hb⟩ := hsep (fun i => i.elim0) u
  have hb' : ∀ x : M, memM x b ↔ ¬ memM x x := by
    intro x
    rw [hb x]
    simp [hu x]
  exact (fun hbb => (hb' b).1 hbb hbb) ((hb' b).2 (fun hbb => (hb' b).1 hbb hbb))

/-- Consistency of any extension of ZFC — in particular of `ZFC` together with an axiom
asserting the existence of an inaccessible cardinal — implies the consistency of ZFC. -/
theorem ConZFC_of_extension {T : setLang.Theory} (hT : ZFC ⊆ T) (h : T.IsSatisfiable) :
    ZFC.IsSatisfiable :=
  h.mono hT

end Frontier

import Mathlib

/-!
# The first-order language of set theory and the axioms of ZFC

This file sets up the first-order language `Frontier.setLang` with a single binary relation
symbol `∈`, convenient combinators for building formulas (`allQ`, `exQ`, `memF`, `up`), and
the theory `Frontier.ZFC` consisting of

* extensionality, pairing, union, power set, infinity, foundation, choice, and
* the separation and replacement schemes (one instance for every formula with parameters).

For each axiom we prove a `Realize` lemma expressing satisfaction in an arbitrary structure in
readable mathematical terms.
-/

open FirstOrder Language

namespace Frontier

/-- The type of relation symbols of the language of set theory: one binary symbol. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: one binary relation symbol. -/
def setLang : Language := ⟨fun _ => Empty, memRel⟩

/-- The membership relation symbol. -/
abbrev memSymb : setLang.Relations 2 := memRel.mem

variable {α : Type*}

/-- The innermost bound variable. -/
abbrev vz : setLang.Term (α ⊕ Unit) := Term.var (Sum.inr ())

/-- Lift a term past one binder. -/
def up (t : setLang.Term α) : setLang.Term (α ⊕ Unit) := t.relabel Sum.inl

/-- The atomic formula `t₁ ∈ t₂`. -/
def memF (t₁ t₂ : setLang.Term α) : setLang.Formula α := memSymb.formula₂ t₁ t₂

/-- Universal quantification over the innermost variable. -/
noncomputable def allQ (φ : setLang.Formula (α ⊕ Unit)) : setLang.Formula α := Formula.iAlls Unit φ

/-- Existential quantification over the innermost variable. -/
noncomputable def exQ (φ : setLang.Formula (α ⊕ Unit)) : setLang.Formula α := Formula.iExs Unit φ

section Semantics

variable {M : Type*} [setLang.Structure M]

/-- The interpretation of the membership symbol in a structure. -/
def memM (x y : M) : Prop := Structure.RelMap memSymb ![x, y]

@[simp] theorem realize_memF {t₁ t₂ : setLang.Term α} {v : α → M} :
    (memF t₁ t₂).Realize v ↔ memM (t₁.realize v) (t₂.realize v) := by
  simp [memF, memM]

@[simp] theorem realize_up {t : setLang.Term α} {v : α → M} {x : M} :
    (up t).realize (Sum.elim v (fun _ => x)) = t.realize v := by
  simp [up, Term.realize_relabel, Function.comp_def]

omit [setLang.Structure M] in
theorem elim_unit_ext {v : α → M} {i : Unit → M} :
    Sum.elim v (fun _ => i ()) = Sum.elim v i := by
  funext a
  cases a with
  | inl a => rfl
  | inr b => cases b; rfl

@[simp] theorem realize_allQ {φ : setLang.Formula (α ⊕ Unit)} {v : α → M} :
    (allQ φ).Realize v ↔ ∀ x : M, φ.Realize (Sum.elim v (fun _ => x)) := by
  simp only [allQ, Formula.realize_iAlls]
  exact ⟨fun h x => by simpa using h (fun _ => x), fun h i => by
    have := h (i ()); rwa [elim_unit_ext] at this⟩

@[simp] theorem realize_exQ {φ : setLang.Formula (α ⊕ Unit)} {v : α → M} :
    (exQ φ).Realize v ↔ ∃ x : M, φ.Realize (Sum.elim v (fun _ => x)) := by
  simp only [exQ, Formula.realize_iExs]
  exact ⟨fun ⟨i, h⟩ => ⟨i (), by rwa [elim_unit_ext]⟩,
    fun ⟨x, h⟩ => ⟨fun _ => x, by simpa using h⟩⟩

end Semantics

/-! ### The finitely many non-scheme axioms -/

/-- Extensionality: `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
noncomputable def axExt : setLang.Sentence :=
  allQ (allQ ((allQ ((memF vz (up (up vz))).iff (memF vz (up vz)))).imp (Term.equal (up vz) vz)))

/-- Pairing: `∀ x y, ∃ p, ∀ z, z ∈ p ↔ (z = x ∨ z = y)`. -/
noncomputable def axPair : setLang.Sentence :=
  allQ (allQ (exQ (allQ ((memF vz (up vz)).iff
    ((Term.equal vz (up (up (up vz)))) ⊔ (Term.equal vz (up (up vz))))))))

/-- Union: `∀ a, ∃ u, ∀ z, z ∈ u ↔ ∃ y, y ∈ a ∧ z ∈ y`. -/
noncomputable def axUnion : setLang.Sentence :=
  allQ (exQ (allQ ((memF vz (up vz)).iff
    (exQ ((memF vz (up (up (up vz)))) ⊓ (memF (up vz) vz))))))

/-- Power set: `∀ a, ∃ p, ∀ z, z ∈ p ↔ ∀ w, w ∈ z → w ∈ a`. -/
noncomputable def axPow : setLang.Sentence :=
  allQ (exQ (allQ ((memF vz (up vz)).iff
    (allQ ((memF vz (up vz)).imp (memF vz (up (up (up vz)))))))))

/-- Infinity: there is a set containing the empty set and closed under `x ↦ x ∪ {x}`. -/
noncomputable def axInf : setLang.Sentence :=
  exQ ((exQ ((memF vz (up vz)) ⊓ (allQ (Formula.not (memF vz (up vz)))))) ⊓
    (allQ ((memF vz (up vz)).imp (exQ ((memF vz (up (up vz))) ⊓
      (allQ ((memF vz (up vz)).iff
        ((memF vz (up (up vz))) ⊔ (Term.equal vz (up (up vz)))))))))))

/-- Foundation: every nonempty set has an `∈`-minimal element. -/
noncomputable def axFound : setLang.Sentence :=
  allQ ((exQ (memF vz (up vz))).imp
    (exQ ((memF vz (up vz)) ⊓
      (allQ ((memF vz (up vz)).imp (Formula.not (memF vz (up (up vz)))))))))

/-- Choice: every family of nonempty, pairwise disjoint sets admits a selector. -/
noncomputable def axChoice : setLang.Sentence :=
  allQ ((((allQ ((memF vz (up vz)).imp (exQ (memF vz (up vz))))) ⊓
      (allQ (allQ ((((memF (up vz) (up (up vz))) ⊓ (memF vz (up (up vz)))) ⊓
        (Formula.not (Term.equal (up vz) vz))).imp
          (allQ ((memF vz (up (up vz))).imp (Formula.not (memF vz (up vz)))))))))).imp
    (exQ (allQ ((memF vz (up (up vz))).imp
      (exQ (((memF vz (up vz)) ⊓ (memF vz (up (up vz)))) ⊓
        (allQ (((memF vz (up (up vz))) ⊓ (memF vz (up (up (up vz))))).imp
          (Term.equal vz (up vz))))))))))

/-! ### The axiom schemes -/

/-- Relabelling used to insert a separation formula (with `n` parameters and one free variable)
into the scope of the three binders `a`, `b`, `x`. -/
def sepRel (n : ℕ) : (Fin n ⊕ Unit) → (((Fin n ⊕ Unit) ⊕ Unit) ⊕ Unit)
  | Sum.inl i => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inr _ => Sum.inr ()

/-- An instance of the separation scheme:
`∀ p⃗ a, ∃ b, ∀ x, x ∈ b ↔ (x ∈ a ∧ φ(x, p⃗))`. -/
noncomputable def axSep (n : ℕ) (φ : setLang.Formula (Fin n ⊕ Unit)) : setLang.Sentence :=
  Formula.iAlls (Fin n)
    (Formula.relabel Sum.inr
      (allQ (exQ (allQ ((memF vz (up vz)).iff
        ((memF vz (up (up vz))) ⊓ (Formula.relabel (sepRel n) φ)))))))

/-- Relabelling of a replacement formula `φ(x, y, p⃗)` into the scope of `a, x, y, y'`,
sending `y` to the variable `y`. -/
def repRel₁ (n : ℕ) : (Fin n ⊕ Bool) → ((((Fin n ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit)
  | Sum.inl i => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | Sum.inr false => Sum.inl (Sum.inl (Sum.inr ()))
  | Sum.inr true => Sum.inl (Sum.inr ())

/-- Relabelling of a replacement formula `φ(x, y, p⃗)` into the scope of `a, x, y, y'`,
sending `y` to the variable `y'`. -/
def repRel₂ (n : ℕ) : (Fin n ⊕ Bool) → ((((Fin n ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit)
  | Sum.inl i => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | Sum.inr false => Sum.inl (Sum.inl (Sum.inr ()))
  | Sum.inr true => Sum.inr ()

/-- Relabelling of a replacement formula `φ(x, y, p⃗)` into the scope of `a, b, y, x`. -/
def repRel₃ (n : ℕ) : (Fin n ⊕ Bool) → ((((Fin n ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit)
  | Sum.inl i => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | Sum.inr false => Sum.inr ()
  | Sum.inr true => Sum.inl (Sum.inr ())

/-- An instance of the replacement scheme: if `φ(x, y, p⃗)` is functional on `a`, then the
image of `a` is a set. -/
noncomputable def axRep (n : ℕ) (φ : setLang.Formula (Fin n ⊕ Bool)) : setLang.Sentence :=
  Formula.iAlls (Fin n)
    (Formula.relabel Sum.inr
      (allQ
        ((allQ (allQ (allQ ((((memF (up (up vz)) (up (up (up vz)))) ⊓
            (Formula.relabel (repRel₁ n) φ)) ⊓ (Formula.relabel (repRel₂ n) φ)).imp
              (Term.equal (up vz) vz))))).imp
          (exQ (allQ ((memF vz (up vz)).iff
            (exQ ((memF vz (up (up (up vz)))) ⊓ (Formula.relabel (repRel₃ n) φ)))))))))

/-- The theory ZFC. -/
def ZFC : setLang.Theory :=
  {axExt, axPair, axUnion, axPow, axInf, axFound, axChoice} ∪
    (Set.range fun p : (n : ℕ) × setLang.Formula (Fin n ⊕ Unit) => axSep p.1 p.2) ∪
    (Set.range fun p : (n : ℕ) × setLang.Formula (Fin n ⊕ Bool) => axRep p.1 p.2)

/-! ### Satisfaction of the axioms -/

section Realize

variable {M : Type*} [setLang.Structure M]

@[simp] theorem realize_axExt :
    M ⊨ axExt ↔ ∀ x y : M, (∀ z, memM z x ↔ memM z y) → x = y := by
  simp [axExt, Sentence.Realize]

@[simp] theorem realize_axPair :
    M ⊨ axPair ↔ ∀ x y : M, ∃ p, ∀ z, memM z p ↔ (z = x ∨ z = y) := by
  simp [axPair, Sentence.Realize]

@[simp] theorem realize_axUnion :
    M ⊨ axUnion ↔ ∀ a : M, ∃ u, ∀ z, memM z u ↔ ∃ y, memM y a ∧ memM z y := by
  simp [axUnion, Sentence.Realize]

@[simp] theorem realize_axPow :
    M ⊨ axPow ↔ ∀ a : M, ∃ p, ∀ z, memM z p ↔ ∀ w, memM w z → memM w a := by
  simp [axPow, Sentence.Realize]

@[simp] theorem realize_axInf :
    M ⊨ axInf ↔ ∃ a : M, (∃ e, memM e a ∧ ∀ z, ¬ memM z e) ∧
      ∀ x, memM x a → ∃ y, memM y a ∧ ∀ z, memM z y ↔ (memM z x ∨ z = x) := by
  simp [axInf, Sentence.Realize]

@[simp] theorem realize_axFound :
    M ⊨ axFound ↔ ∀ a : M, (∃ x, memM x a) → ∃ x, memM x a ∧ ∀ y, memM y x → ¬ memM y a := by
  simp [axFound, Sentence.Realize]

@[simp] theorem realize_axChoice :
    M ⊨ axChoice ↔ ∀ a : M,
      ((∀ x, memM x a → ∃ z, memM z x) ∧
        (∀ x y, ((memM x a ∧ memM y a) ∧ ¬ x = y) → ∀ z, memM z x → ¬ memM z y)) →
      ∃ c, ∀ x, memM x a →
        ∃ z, (memM z x ∧ memM z c) ∧ ∀ w, (memM w x ∧ memM w c) → w = z := by
  simp [axChoice, Sentence.Realize]

@[simp] theorem realize_axSep (n : ℕ) (φ : setLang.Formula (Fin n ⊕ Unit)) :
    M ⊨ axSep n φ ↔ ∀ p : Fin n → M, ∀ a : M, ∃ b : M, ∀ x : M,
      memM x b ↔ (memM x a ∧ φ.Realize (Sum.elim p (fun _ => x))) := by
  simp only [axSep, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
    realize_allQ, realize_exQ, Formula.realize_iff, realize_memF, realize_up, Term.realize_var,
    Formula.realize_inf, Sum.elim_inr]
  refine forall_congr' fun p => forall_congr' fun a => exists_congr fun b => forall_congr' fun x =>
    iff_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [iff_iff_eq]
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr u => cases u; rfl

@[simp] theorem realize_axRep (n : ℕ) (φ : setLang.Formula (Fin n ⊕ Bool)) :
    M ⊨ axRep n φ ↔ ∀ p : Fin n → M, ∀ a : M,
      (∀ x y y' : M, ((memM x a ∧ φ.Realize (Sum.elim p (fun b => cond b y x))) ∧
          φ.Realize (Sum.elim p (fun b => cond b y' x))) → y = y') →
      ∃ b : M, ∀ y : M, memM y b ↔ ∃ x : M, memM x a ∧
        φ.Realize (Sum.elim p (fun c => cond c y x)) := by
  simp only [axRep, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
    realize_allQ, realize_exQ, Formula.realize_iff, realize_memF, realize_up, Term.realize_var,
    Formula.realize_inf, Formula.realize_imp, Sum.elim_inr]
  refine forall_congr' fun p => ?_
  refine forall_congr' fun a => ?_
  refine imp_congr ?_ ?_
  · refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun y' => ?_
    refine imp_congr ?_ Iff.rfl
    refine and_congr (and_congr Iff.rfl ?_) ?_
    · rw [iff_iff_eq]; congr 1
      funext i
      cases i with
      | inl i => rfl
      | inr b => cases b <;> rfl
    · rw [iff_iff_eq]; congr 1
      funext i
      cases i with
      | inl i => rfl
      | inr b => cases b <;> rfl
  · refine exists_congr fun b => forall_congr' fun y => ?_
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr Iff.rfl ?_)
    rw [iff_iff_eq]; congr 1
    funext i
    cases i with
    | inl i => rfl
    | inr c => cases c <;> rfl

theorem models_ZFC_iff :
    M ⊨ ZFC ↔ (M ⊨ axExt ∧ M ⊨ axPair ∧ M ⊨ axUnion ∧ M ⊨ axPow ∧ M ⊨ axInf ∧
      M ⊨ axFound ∧ M ⊨ axChoice) ∧
      (∀ n (φ : setLang.Formula (Fin n ⊕ Unit)), M ⊨ axSep n φ) ∧
      (∀ n (φ : setLang.Formula (Fin n ⊕ Bool)), M ⊨ axRep n φ) := by
  constructor
  · intro h
    haveI := h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      [skip; skip; skip; skip; skip; skip; skip; (intro n φ); (intro n φ)] <;>
      refine Theory.realize_sentence_of_mem ZFC ?_ <;> simp only [ZFC, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inr ⟨⟨n, φ⟩, rfl⟩)
    · exact Or.inr ⟨⟨n, φ⟩, rfl⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hsep, hrep⟩
    refine ⟨fun {σ} hσ => ?_⟩
    simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hσ
    rcases hσ with ((h | ⟨p, rfl⟩) | ⟨p, rfl⟩)
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · exact hsep p.1 p.2
    · exact hrep p.1 p.2

end Realize

end Frontier

