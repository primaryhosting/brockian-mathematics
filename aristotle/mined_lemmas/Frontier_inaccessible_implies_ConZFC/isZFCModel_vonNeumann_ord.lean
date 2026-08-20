/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

universe u

namespace Frontier

open Cardinal Ordinal ZFSet Order

/-- `IsZFCModel M` says that the ZFC set `M`, equipped with the inherited membership
relation, is a model of ZFC: every axiom of ZFC, *relativized to* `M` (all quantifiers
bounded by `M`), holds.

The separation and replacement schemes are stated in their *second-order* form, i.e. for
arbitrary (meta-level) predicates and functions; this is stronger than the first-order
schemes, whose instances are obtained by taking the predicate/function defined by a
formula. Choice is stated in Zermelo's transversal form (every family of pairwise disjoint
nonempty sets has a choice set), which is equivalent to the axiom of choice over ZF. -/
structure IsZFCModel (M : ZFSet.{u}) : Prop where
  /-- The model is nonempty. -/
  nonempty : ∃ x, x ∈ M
  /-- The domain is transitive, so that membership is absolute. -/
  transitive : M.IsTransitive
  /-- Extensionality. -/
  ext : ∀ x ∈ M, ∀ y ∈ M, (∀ z ∈ M, z ∈ x ↔ z ∈ y) → x = y
  /-- Existence of the empty set. -/
  empty : ∃ e ∈ M, ∀ z ∈ M, z ∉ e
  /-- Pairing. -/
  pairing : ∀ x ∈ M, ∀ y ∈ M, ∃ p ∈ M, ∀ z ∈ M, (z ∈ p ↔ z = x ∨ z = y)
  /-- Union. -/
  union : ∀ x ∈ M, ∃ u ∈ M, ∀ z ∈ M, (z ∈ u ↔ ∃ y ∈ M, y ∈ x ∧ z ∈ y)
  /-- Power set. -/
  powerset : ∀ x ∈ M, ∃ p ∈ M, ∀ z ∈ M, (z ∈ p ↔ ∀ w ∈ M, w ∈ z → w ∈ x)
  /-- Infinity: there is an inductive set. -/
  infinity : ∃ i ∈ M, (∃ e ∈ M, e ∈ i ∧ ∀ z ∈ M, z ∉ e) ∧
      ∀ x ∈ M, x ∈ i → ∃ y ∈ M, y ∈ i ∧ ∀ z ∈ M, (z ∈ y ↔ z ∈ x ∨ z = x)
  /-- Separation, in second-order form. -/
  separation : ∀ (p : ZFSet.{u} → Prop), ∀ x ∈ M, ∃ s ∈ M, ∀ z ∈ M, (z ∈ s ↔ z ∈ x ∧ p z)
  /-- Replacement, in second-order form. -/
  replacement : ∀ (F : ZFSet.{u} → ZFSet.{u}), ∀ x ∈ M, (∀ a ∈ M, a ∈ x → F a ∈ M) →
      ∃ r ∈ M, ∀ z ∈ M, (z ∈ r ↔ ∃ a ∈ M, a ∈ x ∧ F a = z)
  /-- Foundation. -/
  foundation : ∀ x ∈ M, (∃ z ∈ M, z ∈ x) → ∃ y ∈ M, y ∈ x ∧ ∀ z ∈ M, z ∈ y → z ∉ x
  /-- Choice, in Zermelo's transversal form. -/
  choice : ∀ x ∈ M, (∀ y ∈ M, y ∈ x → ∃ z ∈ M, z ∈ y) →
      (∀ y ∈ M, ∀ y' ∈ M, y ∈ x → y' ∈ x → y ≠ y' → ¬ ∃ z ∈ M, z ∈ y ∧ z ∈ y') →
      ∃ c ∈ M, ∀ y ∈ M, y ∈ x → ∃! z, z ∈ M ∧ z ∈ y ∧ z ∈ c

/-! ### Cardinal arithmetic below an inaccessible -/

/-- Below an inaccessible cardinal `κ`, all the stages `V_ a` of the cumulative hierarchy
have size `< κ`: this is `preBeth a < κ` for `a < κ.ord`. Strong limitness handles the
successor step and regularity the limit step. -/

theorem isZFCModel_vonNeumann_ord {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    IsZFCModel (V_ κ.ord) := by
  have hlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_lt.le
  have htr : (V_ κ.ord).IsTransitive := isTransitive_vonNeumann _
  have hpos : (0 : Ordinal) < κ.ord := hlim.bot_lt
  have hmem : ∀ {y : ZFSet.{u}}, y ∈ V_ κ.ord ↔ y.rank < κ.ord := fun {_} => mem_vonNeumann
  have hempty : (∅ : ZFSet.{u}) ∈ V_ κ.ord := by rw [hmem, rank_empty]; exact hpos
  refine ⟨⟨∅, hempty⟩, htr, ?_, ⟨∅, hempty, by simp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- extensionality
    intro x hx y hy h
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => (h z (htr.mem_trans hz hx)).1 hz, fun hz => (h z (htr.mem_trans hz hy)).2 hz⟩
  · -- pairing
    intro x hx y hy
    refine ⟨{x, y}, ?_, fun z _ => mem_pair⟩
    rw [hmem, rank_pair]
    exact max_lt (hlim.succ_lt (hmem.1 hx)) (hlim.succ_lt (hmem.1 hy))
  · -- union
    intro x hx
    refine ⟨⋃₀ x, hmem.2 ((rank_sUnion_le x).trans_lt (hmem.1 hx)), ?_⟩
    intro z _
    rw [mem_sUnion]
    exact ⟨fun ⟨y, hyx, hzy⟩ => ⟨y, htr.mem_trans hyx hx, hyx, hzy⟩,
      fun ⟨y, _, hyx, hzy⟩ => ⟨y, hyx, hzy⟩⟩
  · -- power set
    intro x hx
    refine ⟨ZFSet.powerset x, hmem.2 (by rw [rank_powerset]; exact hlim.succ_lt (hmem.1 hx)), ?_⟩
    intro z hz
    rw [mem_powerset]
    exact ⟨fun hsub w _ hwz => hsub hwz, fun h w hwz => h w (htr.mem_trans hwz hz) hwz⟩
  · -- infinity
    have homega : (Ordinal.omega0).toZFSet ∈ V_ κ.ord := by
      rw [hmem, rank_toZFSet, ← Cardinal.ord_aleph0]
      exact Cardinal.ord_lt_ord.2 hκ.aleph0_lt
    refine ⟨_, homega, ⟨∅, hempty, ?_, by simp⟩, ?_⟩
    · rw [mem_toZFSet_iff]
      exact ⟨0, omega0_pos, toZFSet_zero⟩
    · intro x hx hxi
      refine ⟨insert x x, ?_, ?_, fun z _ => mem_insert_iff.trans (by tauto)⟩
      · rw [hmem, rank_insert, max_lt_iff]
        exact ⟨hlim.succ_lt (hmem.1 hx), hmem.1 hx⟩
      · obtain ⟨a, ha, rfl⟩ := mem_toZFSet_iff.1 hxi
        rw [← toZFSet_succ, mem_toZFSet_iff]
        exact ⟨succ a, isSuccLimit_omega0.succ_lt ha, rfl⟩
  · -- separation
    intro p x hx
    refine ⟨ZFSet.sep p x, ?_, fun z _ => mem_sep⟩
    exact hmem.2 (lt_of_le_of_lt (rank_mono fun z hz => (mem_sep.1 hz).1) (hmem.1 hx))
  · -- replacement
    intro F x hx hF
    refine ⟨ZFSet.range
      (fun i : Shrink.{u} x => F (((equivShrink.{u} x).symm i : ZFSet.{u}))), ?_, ?_⟩
    · rw [hmem, rank_range]
      apply iSup_lt_ord_of_mem_vonNeumann hκ hx
      intro i
      have ha : ((equivShrink.{u} x).symm i : ZFSet.{u}) ∈ x := ((equivShrink _).symm i).2
      exact hlim.succ_lt (hmem.1 (hF _ (htr.mem_trans ha hx) ha))
    · intro z _
      rw [ZFSet.mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        have ha : ((equivShrink.{u} x).symm i : ZFSet.{u}) ∈ x := ((equivShrink _).symm i).2
        exact ⟨_, htr.mem_trans ha hx, ha, rfl⟩
      · rintro ⟨a, -, hax, rfl⟩
        exact ⟨equivShrink.{u} x ⟨a, hax⟩, by simp⟩
  · -- foundation
    intro x hx hne
    obtain ⟨z, -, hzx⟩ := hne
    obtain ⟨y, hyx, hinter⟩ := ZFSet.regularity x
      (by intro h; rw [h] at hzx; exact ZFSet.notMem_empty z hzx)
    refine ⟨y, htr.mem_trans hyx hx, hyx, ?_⟩
    intro w _ hwy hwx
    have hw : w ∈ x ∩ y := by rw [ZFSet.mem_inter]; exact ⟨hwx, hwy⟩
    rw [hinter] at hw
    exact ZFSet.notMem_empty w hw
  · -- choice
    intro x hx hne hdisj
    have key : ∀ a : ↥x, ∃ z, z ∈ (a : ZFSet.{u}) := by
      intro a
      obtain ⟨z, -, hz⟩ := hne a (htr.mem_trans a.2 hx) a.2
      exact ⟨z, hz⟩
    choose g hg using key
    refine ⟨ZFSet.range (fun i : Shrink.{u} x => g ((equivShrink.{u} x).symm i)), ?_, ?_⟩
    · rw [hmem, rank_range]
      apply iSup_lt_ord_of_mem_vonNeumann hκ hx
      intro i
      have h1 : (g ((equivShrink.{u} x).symm i)).rank
          < ((equivShrink.{u} x).symm i : ZFSet.{u}).rank := rank_lt_of_mem (hg _)
      have h2 : ((equivShrink.{u} x).symm i : ZFSet.{u}).rank < κ.ord :=
        hmem.1 (htr.mem_trans ((equivShrink _).symm i).2 hx)
      exact hlim.succ_lt (h1.trans h2)
    · intro y hy hyx
      refine ⟨g ⟨y, hyx⟩, ⟨htr.mem_trans (hg ⟨y, hyx⟩) hy, hg _, ?_⟩, ?_⟩
      · rw [ZFSet.mem_range]
        exact ⟨equivShrink.{u} x ⟨y, hyx⟩, by simp⟩
      · rintro z ⟨hzM, hzy, hzc⟩
        rw [ZFSet.mem_range] at hzc
        obtain ⟨i, rfl⟩ := hzc
        set a := ((equivShrink.{u} x).symm i) with ha
        have haM : (a : ZFSet.{u}) ∈ V_ κ.ord := htr.mem_trans a.2 hx
        have hay : (a : ZFSet.{u}) = y := by
          by_contra hne'
          exact hdisj a haM y hy a.2 hyx hne' ⟨g a, hzM, hg a, hzy⟩
        subst hay
        rfl


/-! ### The first-order language of set theory -/

open FirstOrder Language

/-- The type of relation symbols of the language of set theory: a single binary
membership relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The (purely relational) first-order language of set theory. -/
