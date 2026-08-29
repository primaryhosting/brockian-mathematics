/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

universe u

namespace Frontier

open Cardinal Ordinal ZFSet Order

/-- The axioms of ZFC, stated for an arbitrary membership relation `mem` on a type `M`.

Separation and Replacement are stated in their *second-order* (schematic over all
ambient predicates/functions) form, which implies every first-order instance. -/
structure IsZFCModel {M : Type*} (mem : M → M → Prop) : Prop where
  /-- Extensionality. -/
  extensionality : ∀ x y : M, (∀ z, mem z x ↔ mem z y) → x = y
  /-- Foundation (regularity). -/
  foundation : ∀ x : M, (∃ z, mem z x) → ∃ y, mem y x ∧ ∀ z, mem z y → ¬ mem z x
  /-- Existence of the empty set. -/
  empty : ∃ e : M, ∀ z, ¬ mem z e
  /-- Pairing. -/
  pairing : ∀ x y : M, ∃ p : M, ∀ z, mem z p ↔ (z = x ∨ z = y)
  /-- Union. -/
  union : ∀ x : M, ∃ u : M, ∀ z, mem z u ↔ ∃ y, mem y x ∧ mem z y
  /-- Power set. -/
  powerset : ∀ x : M, ∃ p : M, ∀ z, mem z p ↔ ∀ w, mem w z → mem w x
  /-- Infinity: there is a set containing the empty set and closed under `y ↦ y ∪ {y}`. -/
  infinity : ∃ i : M, (∃ e, mem e i ∧ ∀ z, ¬ mem z e) ∧
      ∀ y, mem y i → ∃ s, mem s i ∧ ∀ z, mem z s ↔ (mem z y ∨ z = y)
  /-- Separation. -/
  separation : ∀ (P : M → Prop) (x : M), ∃ y : M, ∀ z, mem z y ↔ (mem z x ∧ P z)
  /-- Replacement. -/
  replacement : ∀ (F : M → M) (x : M), ∃ y : M, ∀ z, mem z y ↔ ∃ w, mem w x ∧ z = F w
  /-- Choice: every set of pairwise disjoint nonempty sets has a transversal. -/
  choice : ∀ x : M, (∀ y, mem y x → ∃ z, mem z y) →
      (∀ y y', mem y x → mem y' x → y ≠ y' → ∀ z, ¬(mem z y ∧ mem z y')) →
      ∃ c : M, ∀ y, mem y x → ∃ z, mem z y ∧ mem z c ∧ ∀ z', mem z' y → mem z' c → z' = z

/-- The `o`-th level of the von Neumann hierarchy, as a type. -/
def VLevel (o : Ordinal.{u}) : Type (u + 1) := {x : ZFSet.{u} // x.rank < o}

/-- Membership on `VLevel o`, inherited from `ZFSet`. -/
def VMem (o : Ordinal.{u}) : VLevel o → VLevel o → Prop := fun a b => (a.1 ∈ b.1)

namespace VLevel

variable {o : Ordinal.{u}}

@[ext]
theorem ext {a b : VLevel o} (h : a.1 = b.1) : a = b := Subtype.ext h

theorem eq_iff {a b : VLevel o} : a = b ↔ a.1 = b.1 := Subtype.ext_iff

theorem mem_iff {a b : VLevel o} : VMem o a b ↔ a.1 ∈ b.1 := Iff.rfl

/-- Elements of an element of `VLevel o` have rank `< o`. -/
theorem rank_lt_of_mem {b : VLevel o} {w : ZFSet.{u}} (hw : w ∈ b.1) : w.rank < o :=
  (ZFSet.rank_lt_of_mem hw).trans b.2

end VLevel

/-! ### Cardinality bounds below an inaccessible -/

/-- Below an inaccessible cardinal, all the beth numbers stay below it. -/
theorem preBeth_lt_of_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ∀ a : Ordinal.{u}, a < κ.ord → preBeth a < κ := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => intro _; simpa using hκ.pos
  | succ b ih =>
      intro h
      rw [preBeth_succ]
      exact hκ.isStrongLimit.two_power_lt (ih ((Order.lt_succ b).trans h))
  | limit b hb ih =>
      intro h
      rw [preBeth_limit hb.isSuccPrelimit,
        ← Equiv.iSup_comp (g := fun c : Set.Iio b => preBeth c)
          (Ordinal.ToType.mk (o := b)).symm.toEquiv]
      refine Cardinal.iSup_lt_of_isRegular hκ.isRegular ?_
        (fun i => ih _ ((Ordinal.ToType.mk (o := b)).symm.toEquiv i).2
          (((Ordinal.ToType.mk (o := b)).symm.toEquiv i).2.trans h))
      rw [mk_toType]
      exact Cardinal.lt_ord.1 h

/-- Any set of rank below `κ.ord`, for `κ` inaccessible, has cardinality below `κ`. -/
theorem card_lt_of_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x.rank < κ.ord) : x.card < κ :=
  lt_of_le_of_lt
    (by simpa [ZFSet.card_vonNeumann] using ZFSet.card_mono x.subset_vonNeumann_self)
    (preBeth_lt_of_inaccessible hκ _ hx)

/-! ### The axioms hold in `V_κ` -/

variable {κ : Cardinal.{u}}

theorem isSuccLimit_ord_of_inaccessible (hκ : κ.IsInaccessible) : IsSuccLimit κ.ord :=
  isSuccLimit_ord hκ.isRegular.aleph0_le

/-- Ranges of small families of sets of small rank have small rank. -/
theorem rank_range_lt (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x.rank < κ.ord)
    (g : Shrink.{u} (x : Type (u + 1)) → ZFSet.{u}) (hg : ∀ i, (g i).rank < κ.ord) :
    (ZFSet.range g).rank < κ.ord := by
  rw [ZFSet.rank_range]
  refine Cardinal.iSup_lt_ord_of_isRegular hκ.isRegular ?_
    (fun i => (isSuccLimit_ord_of_inaccessible hκ).succ_lt (hg i))
  exact card_lt_of_rank_lt hκ hx

theorem vlevel_extensionality (hκ : κ.IsInaccessible) :
    ∀ x y : VLevel κ.ord, (∀ z, VMem κ.ord z x ↔ VMem κ.ord z y) → x = y := by
  intro x y h
  refine VLevel.ext (ZFSet.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩)
  · exact (h ⟨w, VLevel.rank_lt_of_mem hw⟩).1 hw
  · exact (h ⟨w, VLevel.rank_lt_of_mem hw⟩).2 hw

theorem vlevel_foundation (hκ : κ.IsInaccessible) :
    ∀ x : VLevel κ.ord, (∃ z, VMem κ.ord z x) →
      ∃ y, VMem κ.ord y x ∧ ∀ z, VMem κ.ord z y → ¬ VMem κ.ord z x := by
  rintro x ⟨z, hz⟩
  have hne : x.1 ≠ ∅ := by
    intro h
    rw [VLevel.mem_iff, h] at hz
    exact ZFSet.notMem_empty _ hz
  obtain ⟨y, hy, hxy⟩ := ZFSet.regularity x.1 hne
  refine ⟨⟨y, VLevel.rank_lt_of_mem hy⟩, hy, fun w hwy hwx => ?_⟩
  have hmem : w.1 ∈ x.1 ∩ y := ZFSet.mem_inter.2 ⟨hwx, hwy⟩
  rw [hxy] at hmem
  exact ZFSet.notMem_empty _ hmem

theorem vlevel_empty (hκ : κ.IsInaccessible) :
    ∃ e : VLevel κ.ord, ∀ z, ¬ VMem κ.ord z e := by
  refine ⟨⟨∅, ?_⟩, fun z hz => ZFSet.notMem_empty _ hz⟩
  rw [ZFSet.rank_empty]
  exact hκ.isRegular.ord_pos

theorem vlevel_pairing (hκ : κ.IsInaccessible) :
    ∀ x y : VLevel κ.ord, ∃ p : VLevel κ.ord, ∀ z, VMem κ.ord z p ↔ (z = x ∨ z = y) := by
  intro x y
  have hlim := isSuccLimit_ord_of_inaccessible hκ
  refine ⟨⟨{x.1, y.1}, ?_⟩, fun z => ?_⟩
  · rw [ZFSet.rank_pair]
    exact max_lt (hlim.succ_lt x.2) (hlim.succ_lt y.2)
  · rw [VLevel.mem_iff, ZFSet.mem_pair, VLevel.eq_iff, VLevel.eq_iff]

theorem vlevel_union (hκ : κ.IsInaccessible) :
    ∀ x : VLevel κ.ord, ∃ u : VLevel κ.ord, ∀ z,
      VMem κ.ord z u ↔ ∃ y, VMem κ.ord y x ∧ VMem κ.ord z y := by
  intro x
  refine ⟨⟨⋃₀ x.1, lt_of_le_of_lt (ZFSet.rank_sUnion_le x.1) x.2⟩, fun z => ?_⟩
  rw [VLevel.mem_iff, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨⟨y, VLevel.rank_lt_of_mem hyx⟩, hyx, hzy⟩
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨y.1, hyx, hzy⟩

theorem vlevel_powerset (hκ : κ.IsInaccessible) :
    ∀ x : VLevel κ.ord, ∃ p : VLevel κ.ord, ∀ z,
      VMem κ.ord z p ↔ ∀ w, VMem κ.ord w z → VMem κ.ord w x := by
  intro x
  have hlim := isSuccLimit_ord_of_inaccessible hκ
  refine ⟨⟨ZFSet.powerset x.1, ?_⟩, fun z => ?_⟩
  · rw [ZFSet.rank_powerset]
    exact hlim.succ_lt x.2
  · rw [VLevel.mem_iff, ZFSet.mem_powerset]
    constructor
    · intro h w hw
      exact h hw
    · intro h w hw
      exact h ⟨w, VLevel.rank_lt_of_mem (b := z) hw⟩ hw

theorem vlevel_infinity (hκ : κ.IsInaccessible) :
    ∃ i : VLevel κ.ord, (∃ e, VMem κ.ord e i ∧ ∀ z, ¬ VMem κ.ord z e) ∧
      ∀ y, VMem κ.ord y i → ∃ s, VMem κ.ord s i ∧ ∀ z,
        VMem κ.ord z s ↔ (VMem κ.ord z y ∨ z = y) := by
  have homega : (Ordinal.omega0 : Ordinal.{u}) < κ.ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.2 hκ.aleph0_lt
  refine ⟨⟨(Ordinal.omega0 : Ordinal.{u}).toZFSet, by
      rw [Ordinal.rank_toZFSet]; exact homega⟩, ⟨⟨∅, ?_⟩, ?_⟩, ?_⟩
  · rw [ZFSet.rank_empty]
    exact hκ.isRegular.ord_pos
  · refine ⟨?_, fun z hz => ZFSet.notMem_empty _ hz⟩
    rw [VLevel.mem_iff, Ordinal.mem_toZFSet_iff]
    exact ⟨0, Ordinal.omega0_pos, Ordinal.toZFSet_zero⟩
  · intro y hy
    rw [VLevel.mem_iff, Ordinal.mem_toZFSet_iff] at hy
    obtain ⟨a, ha, hay⟩ := hy
    have hsucc : Order.succ a < Ordinal.omega0 :=
      Ordinal.isSuccLimit_omega0.succ_lt ha
    refine ⟨⟨(Order.succ a).toZFSet, ?_⟩, ?_, fun z => ?_⟩
    · rw [Ordinal.rank_toZFSet]
      exact hsucc.trans homega
    · rw [VLevel.mem_iff, Ordinal.mem_toZFSet_iff]
      exact ⟨Order.succ a, hsucc, rfl⟩
    · rw [VLevel.mem_iff, Ordinal.toZFSet_succ, ZFSet.mem_insert_iff, VLevel.eq_iff, hay,
        VLevel.mem_iff]
      exact or_comm

theorem vlevel_separation (hκ : κ.IsInaccessible) :
    ∀ (P : VLevel κ.ord → Prop) (x : VLevel κ.ord), ∃ y : VLevel κ.ord, ∀ z,
      VMem κ.ord z y ↔ (VMem κ.ord z x ∧ P z) := by
  intro P x
  refine ⟨⟨ZFSet.sep (fun w => ∃ h : w.rank < κ.ord, P ⟨w, h⟩) x.1,
      lt_of_le_of_lt (ZFSet.rank_mono ZFSet.sep_subset) x.2⟩, fun z => ?_⟩
  rw [VLevel.mem_iff, ZFSet.mem_sep]
  constructor
  · rintro ⟨hzx, _, hP⟩
    exact ⟨hzx, hP⟩
  · rintro ⟨hzx, hP⟩
    exact ⟨hzx, z.2, hP⟩

theorem vlevel_replacement (hκ : κ.IsInaccessible) :
    ∀ (F : VLevel κ.ord → VLevel κ.ord) (x : VLevel κ.ord), ∃ y : VLevel κ.ord, ∀ z,
      VMem κ.ord z y ↔ ∃ w, VMem κ.ord w x ∧ z = F w := by
  intro F x
  classical
  set e := equivShrink.{u} (x.1 : Type (u + 1)) with he
  set g : Shrink.{u} (x.1 : Type (u + 1)) → ZFSet.{u} :=
    fun i => (F ⟨(e.symm i).1, VLevel.rank_lt_of_mem (e.symm i).2⟩).1 with hgdef
  refine ⟨⟨ZFSet.range g, rank_range_lt hκ x.2 g fun i => (F _).2⟩, fun z => ?_⟩
  rw [VLevel.mem_iff, ZFSet.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨⟨(e.symm i).1, VLevel.rank_lt_of_mem (e.symm i).2⟩, (e.symm i).2, ?_⟩
    exact VLevel.ext hi.symm
  · rintro ⟨w, hwx, rfl⟩
    refine ⟨e ⟨w.1, hwx⟩, ?_⟩
    simp only [hgdef, Equiv.symm_apply_apply]

theorem vlevel_choice (hκ : κ.IsInaccessible) :
    ∀ x : VLevel κ.ord, (∀ y, VMem κ.ord y x → ∃ z, VMem κ.ord z y) →
      (∀ y y', VMem κ.ord y x → VMem κ.ord y' x → y ≠ y' →
        ∀ z, ¬(VMem κ.ord z y ∧ VMem κ.ord z y')) →
      ∃ c : VLevel κ.ord, ∀ y, VMem κ.ord y x → ∃ z,
        VMem κ.ord z y ∧ VMem κ.ord z c ∧ ∀ z', VMem κ.ord z' y → VMem κ.ord z' c → z' = z := by
  intro x hne hdisj
  classical
  have hsel : ∀ w : (x.1 : Type (u + 1)), ∃ t : ZFSet.{u}, t ∈ w.1 := by
    intro w
    obtain ⟨z, hz⟩ := hne ⟨w.1, VLevel.rank_lt_of_mem w.2⟩ w.2
    exact ⟨z.1, hz⟩
  set e := equivShrink.{u} (x.1 : Type (u + 1)) with he
  set g : Shrink.{u} (x.1 : Type (u + 1)) → ZFSet.{u} := fun i => (hsel (e.symm i)).choose with hgdef
  have hgmem : ∀ i, g i ∈ (e.symm i).1 := fun i => (hsel (e.symm i)).choose_spec
  have hgrank : ∀ i, (g i).rank < κ.ord := fun i =>
    VLevel.rank_lt_of_mem (b := ⟨(e.symm i).1, VLevel.rank_lt_of_mem (e.symm i).2⟩) (hgmem i)
  refine ⟨⟨ZFSet.range g, rank_range_lt hκ x.2 g hgrank⟩, fun y hy => ?_⟩
  have hy' : y.1 ∈ x.1 := hy
  refine ⟨⟨g (e ⟨y.1, hy'⟩), hgrank _⟩, ?_, ?_, ?_⟩
  · have h1 := hgmem (e ⟨y.1, hy'⟩)
    rwa [Equiv.symm_apply_apply] at h1
  · rw [VLevel.mem_iff, ZFSet.mem_range]
    exact ⟨_, rfl⟩
  · rintro z' hz'y hz'c
    rw [VLevel.mem_iff, ZFSet.mem_range] at hz'c
    obtain ⟨i, hi⟩ := hz'c
    have hz'mem : z'.1 ∈ (e.symm i).1 := hi ▸ hgmem i
    have hxmem : (e.symm i).1 ∈ x.1 := (e.symm i).2
    have hyy' : y = (⟨(e.symm i).1, VLevel.rank_lt_of_mem (e.symm i).2⟩ : VLevel κ.ord) := by
      by_contra hne'
      exact hdisj y _ hy hxmem hne' z' ⟨hz'y, hz'mem⟩
    have hsymm : e.symm i = ⟨y.1, hy'⟩ := Subtype.ext (congrArg Subtype.val hyy'.symm)
    have hie : i = e ⟨y.1, hy'⟩ := by rw [← hsymm, Equiv.apply_symm_apply]
    apply VLevel.ext
    rw [← hi, hie]

/-- **If `κ` is inaccessible then `V_κ` is a model of ZFC.** -/
theorem isZFCModel_vlevel (hκ : κ.IsInaccessible) : IsZFCModel (VMem κ.ord) where
  extensionality := vlevel_extensionality hκ
  foundation := vlevel_foundation hκ
  empty := vlevel_empty hκ
  pairing := vlevel_pairing hκ
  union := vlevel_union hκ
  powerset := vlevel_powerset hκ
  infinity := vlevel_infinity hκ
  separation := vlevel_separation hκ
  replacement := vlevel_replacement hκ
  choice := vlevel_choice hκ

/-- **Inaccessible implies Con(ZFC).** -/
theorem inaccessible_implies_ConZFC (h : ∃ κ : Cardinal.{u}, κ.IsInaccessible) :
    ∃ (M : Type (u + 1)) (mem : M → M → Prop), IsZFCModel mem := by
  obtain ⟨κ, hκ⟩ := h
  exact ⟨VLevel κ.ord, VMem κ.ord, isZFCModel_vlevel hκ⟩

end Frontier

