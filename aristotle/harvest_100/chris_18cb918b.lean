/-
Models of ZFC given by suitable classes of ZFC sets.
-/
import RequestProject.SetLanguage

/-!
# Classes of sets that model ZFC

We isolate a set of closure conditions on a class `P : ZFSet.{u} → Prop`
(`Frontier.IsZFCClass`) which guarantee that the structure with domain `{x : ZFSet // P x}`
and the real membership relation is a model of the first-order theory `Frontier.ZFC`.

The conditions are: transitivity, closure under pairing, unions, power sets, the presence of
`ω`, and closure under (second-order) replacement.

The class of *all* sets satisfies these conditions, so `ZFSet.{u}` itself is a model of ZFC.
-/

universe u w

namespace Frontier

open FirstOrder Language ZFSet

/-- The `setLang`-structure on a type equipped with a binary relation. -/
def memStructure {M : Type w} (r : M → M → Prop) : setLang.{u}.Structure M where
  funMap {_} f := PEmpty.elim f
  RelMap {n} R := match n, R.down with
    | 2, memRel.mem => fun v => r (v 0) (v 1)

/-- A class of sets satisfying the closure conditions needed to model ZFC. -/
structure IsZFCClass (P : ZFSet.{u} → Prop) : Prop where
  /-- The class is transitive. -/
  mem_trans : ∀ {x y : ZFSet.{u}}, P x → y ∈ x → P y
  /-- The class is closed under unordered pairs. -/
  pair : ∀ {x y : ZFSet.{u}}, P x → P y → P {x, y}
  /-- The class is closed under unions. -/
  sUnion : ∀ {x : ZFSet.{u}}, P x → P (⋃₀ x)
  /-- The class is closed under power sets. -/
  powerset : ∀ {x : ZFSet.{u}}, P x → P x.powerset
  /-- The class contains `ω`. -/
  omega : P ZFSet.omega
  /-- The class is closed under replacement along arbitrary functions. -/
  replacement : ∀ {a : ZFSet.{u}} (f : ZFSet.{u} → ZFSet.{u}), P a → (∀ y ∈ a, P (f y)) →
    ∃ b, P b ∧ ∀ z, z ∈ b ↔ ∃ y ∈ a, f y = z

namespace IsZFCClass

variable {P : ZFSet.{u} → Prop} (h : IsZFCClass P)
include h

theorem empty : P ∅ := h.mem_trans h.omega ZFSet.omega_zero

theorem subset_closed {x y : ZFSet.{u}} (hx : P x) (hy : y ⊆ x) : P y :=
  h.mem_trans (h.powerset hx) (ZFSet.mem_powerset.2 hy)

theorem sep {x : ZFSet.{u}} (p : ZFSet.{u} → Prop) (hx : P x) : P (ZFSet.sep p x) :=
  h.subset_closed hx ZFSet.sep_subset

end IsZFCClass

/-- The domain of the model attached to a class of sets. -/
def VClass (P : ZFSet.{u} → Prop) : Type (u + 1) := {x : ZFSet.{u} // P x}

instance instStructureVClass (P : ZFSet.{u} → Prop) : setLang.{u + 1}.Structure (VClass P) :=
  memStructure (fun x y : {x : ZFSet.{u} // P x} => x.1 ∈ y.1)

@[simp]
theorem mem'_VClass {P : ZFSet.{u} → Prop} (x y : VClass P) :
    Mem'.{u + 1} x y ↔ (x : {x : ZFSet.{u} // P x}).1 ∈ (y : {x : ZFSet.{u} // P x}).1 :=
  Iff.rfl

namespace VClass

variable {P : ZFSet.{u} → Prop} (h : IsZFCClass P)
include h

theorem models_extAx : VClass P ⊨ extAx.{u + 1} := by
  rw [realize_extAx]
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  refine Subtype.ext (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · exact (hxy ⟨z, h.mem_trans hx hz⟩).1 hz
  · exact (hxy ⟨z, h.mem_trans hy hz⟩).2 hz

theorem models_foundAx : VClass P ⊨ foundAx.{u + 1} := by
  rw [realize_foundAx]
  rintro ⟨x, hx⟩ ⟨⟨y, hy⟩, hyx⟩
  have hne : x ≠ ∅ := by
    rintro rfl
    exact ZFSet.notMem_empty _ hyx
  obtain ⟨w, hw, hint⟩ := ZFSet.regularity x hne
  refine ⟨⟨w, h.mem_trans hx hw⟩, hw, ?_⟩
  rintro ⟨⟨z, hz⟩, h1, h2⟩
  have : z ∈ x ∩ w := ZFSet.mem_inter.2 ⟨h2, h1⟩
  rw [hint] at this
  exact ZFSet.notMem_empty _ this

theorem models_pairAx : VClass P ⊨ pairAx.{u + 1} := by
  rw [realize_pairAx]
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨⟨{x, y}, h.pair hx hy⟩, ?_⟩
  rintro ⟨w, hw⟩
  show w ∈ ({x, y} : ZFSet.{u}) ↔ _
  rw [ZFSet.mem_pair]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (hh | hh) <;> [left; right] <;> exact congrArg Subtype.val hh

theorem models_unionAx : VClass P ⊨ unionAx.{u + 1} := by
  rw [realize_unionAx]
  rintro ⟨a, ha⟩
  refine ⟨⟨⋃₀ a, h.sUnion ha⟩, ?_⟩
  rintro ⟨z, hz⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hya, hzy⟩
    exact ⟨⟨y, h.mem_trans ha hya⟩, hzy, hya⟩
  · rintro ⟨⟨y, hy⟩, hzy, hya⟩
    exact ⟨y, hya, hzy⟩

theorem models_powerAx : VClass P ⊨ powerAx.{u + 1} := by
  rw [realize_powerAx]
  rintro ⟨a, ha⟩
  refine ⟨⟨a.powerset, h.powerset ha⟩, ?_⟩
  rintro ⟨z, hz⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_powerset]
  constructor
  · rintro hsub ⟨t, ht⟩ htz
    exact hsub htz
  · intro hall t htz
    exact hall ⟨t, h.mem_trans hz htz⟩ htz

theorem models_infAx : VClass P ⊨ infAx.{u + 1} := by
  rw [realize_infAx]
  refine ⟨⟨ZFSet.omega, h.omega⟩, ⟨⟨∅, h.empty⟩, ZFSet.omega_zero, ?_⟩, ?_⟩
  · rintro ⟨z, hz⟩
    exact ZFSet.notMem_empty z
  · rintro ⟨y, hy⟩ hyw
    refine ⟨⟨insert y y, h.mem_trans h.omega (ZFSet.omega_succ hyw)⟩, ZFSet.omega_succ hyw, ?_⟩
    rintro ⟨z, hz⟩
    show z ∈ insert y y ↔ _
    rw [ZFSet.mem_insert_iff]
    constructor
    · rintro (rfl | hh)
      · exact Or.inr rfl
      · exact Or.inl hh
    · rintro (hh | hh)
      · exact Or.inr hh
      · exact Or.inl (congrArg Subtype.val hh)

theorem models_choiceAx : VClass P ⊨ choiceAx.{u + 1} := by
  rw [realize_choiceAx]
  rintro ⟨a, ha⟩ ⟨hne, hdisj⟩
  -- a choice function on the members of `a`
  classical
  set g : ZFSet.{u} → ZFSet.{u} := fun x => if hx : ∃ z, z ∈ x then hx.choose else ∅ with hg
  have hgmem : ∀ x : ZFSet.{u}, (∃ z, z ∈ x) → g x ∈ x := by
    intro x hx
    simp only [hg, dif_pos hx]
    exact hx.choose_spec
  have hgP : ∀ y ∈ a, P (g y) := by
    intro y hy
    by_cases hx : ∃ z, z ∈ y
    · exact h.mem_trans (h.mem_trans ha hy) (hgmem y hx)
    · simp only [hg, dif_neg hx]
      exact h.empty
  obtain ⟨c, hc, hcmem⟩ := h.replacement g ha hgP
  refine ⟨⟨c, hc⟩, ?_⟩
  rintro ⟨x, hx⟩ hxa
  have hxne : ∃ z, z ∈ x := by
    obtain ⟨⟨z, hz⟩, hzx⟩ := hne ⟨x, hx⟩ hxa
    exact ⟨z, hzx⟩
  have hgx : g x ∈ x := hgmem x hxne
  refine ⟨⟨g x, h.mem_trans hx hgx⟩, ⟨hgx, (hcmem _).2 ⟨x, hxa, rfl⟩⟩, ?_⟩
  rintro ⟨y', hy'⟩ ⟨hy'x, hy'c⟩
  obtain ⟨x', hx'a, hx'⟩ := (hcmem y').1 hy'c
  have hx'P : P x' := h.mem_trans ha hx'a
  have hxx' : (⟨x, hx⟩ : {x : ZFSet.{u} // P x}) = ⟨x', hx'P⟩ := by
    refine hdisj ⟨x, hx⟩ ⟨x', hx'P⟩ ⟨⟨hxa, hx'a⟩, ⟨y', hy'⟩, hy'x, ?_⟩
    have hx'ne : ∃ z, z ∈ x' := by
      obtain ⟨⟨z, hz⟩, hzx⟩ := hne ⟨x', hx'P⟩ hx'a
      exact ⟨z, hzx⟩
    show y' ∈ x'
    rw [← hx']
    exact hgmem x' hx'ne
  have : x = x' := congrArg Subtype.val hxx'
  subst this
  exact Subtype.ext hx'.symm

theorem models_sepAx (k : ℕ) (φ : setLang.{u + 1}.Formula (Fin k ⊕ Fin 1)) :
    VClass P ⊨ sepAx k φ := by
  classical
  rw [realize_sepAx]
  rintro p ⟨a, ha⟩
  refine ⟨⟨ZFSet.sep (fun w => ∃ hw : P w, φ.Realize (Sum.elim p (fun _ => ⟨w, hw⟩))) a,
    h.sep _ ha⟩, ?_⟩
  rintro ⟨z, hz⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_sep]
  refine and_congr_right fun hza => ⟨?_, ?_⟩
  · rintro ⟨hw, hφ⟩
    exact hφ
  · intro hφ
    exact ⟨hz, hφ⟩

theorem models_replAx (k : ℕ) (φ : setLang.{u + 1}.Formula (Fin k ⊕ Fin 2)) :
    VClass P ⊨ replAx k φ := by
  classical
  rw [realize_replAx]
  rintro p ⟨a, ha⟩ hfun
  set Φ : VClass P → VClass P → Prop := fun x y => φ.Realize (Sum.elim p ![x, y]) with hΦ
  set g : ZFSet.{u} → ZFSet.{u} := fun w =>
    if hw : ∃ y : VClass P, ∃ hw : P w, Φ ⟨w, hw⟩ y then (hw.choose : {x : ZFSet.{u} // P x}).1
    else ∅ with hg
  have hgP : ∀ y ∈ a, P (g y) := by
    intro y _
    by_cases hy : ∃ y' : VClass P, ∃ hy : P y, Φ ⟨y, hy⟩ y'
    · simp only [hg, dif_pos hy]
      exact (hy.choose : {x : ZFSet.{u} // P x}).2
    · simp only [hg, dif_neg hy]
      exact h.empty
  obtain ⟨b₀, hb₀, hb₀mem⟩ := h.replacement g ha hgP
  refine ⟨⟨ZFSet.sep (fun z => ∃ hz : P z, ∃ x : VClass P,
      (x : {x : ZFSet.{u} // P x}).1 ∈ a ∧ Φ x ⟨z, hz⟩) b₀, h.sep _ hb₀⟩, ?_⟩
  rintro ⟨y, hy⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨-, hz, x, hxa, hΦx⟩
    exact ⟨x, hxa, hΦx⟩
  · rintro ⟨x, hxa, hΦx⟩
    have hxP : P (x : {x : ZFSet.{u} // P x}).1 := (x : {x : ZFSet.{u} // P x}).2
    have hex : ∃ y' : VClass P, ∃ hw : P (x : {x : ZFSet.{u} // P x}).1,
        Φ ⟨(x : {x : ZFSet.{u} // P x}).1, hw⟩ y' := ⟨⟨y, hy⟩, hxP, hΦx⟩
    have hgx : g (x : {x : ZFSet.{u} // P x}).1 = y := by
      simp only [hg, dif_pos hex]
      obtain ⟨hw, hΦw⟩ := hex.choose_spec
      have : (⟨(x : {x : ZFSet.{u} // P x}).1, hw⟩ : {x : ZFSet.{u} // P x}) = x := Subtype.ext rfl
      rw [this] at hΦw
      have := hfun x hex.choose ⟨y, hy⟩ ⟨⟨hxa, hΦw⟩, hΦx⟩
      exact congrArg Subtype.val this
    refine ⟨(hb₀mem y).2 ⟨_, hxa, hgx⟩, hy, x, hxa, hΦx⟩

theorem models_ZFC : VClass P ⊨ ZFC.{u + 1} := by
  refine ⟨?_⟩
  rintro σ hσ
  rcases hσ with ((hσ | ⟨k, φ, rfl⟩) | ⟨k, φ, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extAx h
    · exact models_foundAx h
    · exact models_pairAx h
    · exact models_unionAx h
    · exact models_powerAx h
    · exact models_infAx h
    · exact models_choiceAx h
  · exact models_sepAx h k φ
  · exact models_replAx h k φ

end VClass

/-! ### The class of all sets -/

/-- The class of all sets satisfies the closure conditions. -/
theorem isZFCClass_true : IsZFCClass (fun _ : ZFSet.{u} => True) where
  mem_trans := fun _ _ => trivial
  pair := fun _ _ => trivial
  sUnion := fun _ => trivial
  powerset := fun _ => trivial
  omega := trivial
  replacement := by
    intro a f _ _
    classical
    refine ⟨ZFSet.range (fun i : ↥a => f i.1), trivial, fun z => ?_⟩
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩

end Frontier

/-
The sets of rank below an inaccessible cardinal form a model of ZFC.
-/
import RequestProject.ZFCModel

/-!
# `V_κ` for `κ` inaccessible is a ZFC class

We show that if `κ` is a (strongly) inaccessible cardinal, then the class of sets of rank
`< κ.ord` — that is, the level `V_κ` of the von Neumann hierarchy — satisfies the closure
conditions `Frontier.IsZFCClass`, and hence gives a model of ZFC.

The two nontrivial points are:

* `Cardinal.preBeth_lt_of_isInaccessible`: `κ` being a strong limit and regular implies that
  `ℶ'_o < κ` for every `o < κ.ord`; since `ZFSet.card (V_ o) = ℶ'_o`, every set of rank `< κ.ord`
  has cardinality `< κ`;
* closure under replacement then follows from the regularity of `κ`.
-/

universe u

open Cardinal Ordinal ZFSet

namespace Frontier

/-- Reindexing a supremum along an equivalence. -/
theorem iSup_reindex {α : Type*} [SupSet α] {ι ι' : Type*} (e : ι' ≃ ι) (f : ι → α) :
    ⨆ i, f i = ⨆ j, f (e j) :=
  congrArg sSup (e.surjective.range_comp f).symm

/-- Below an inaccessible cardinal, the "pre-beth" function stays below the cardinal. -/
theorem preBeth_lt_of_isInaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → Cardinal.preBeth o < κ := by
  intro o
  induction o using Ordinal.induction with
  | _ o IH =>
    intro ho
    rw [Cardinal.preBeth, iSup_reindex (Ordinal.ToType.mk (o := o)).symm.toEquiv]
    refine Cardinal.iSup_lt_of_isRegular hκ.isRegular ?_ ?_
    · rw [mk_toType]
      exact Cardinal.lt_ord.1 ho
    · intro i
      exact hκ.isStrongLimit.two_power_lt
        (IH _ ((Ordinal.ToType.mk (o := o)).symm i).2
          (((Ordinal.ToType.mk (o := o)).symm i).2.trans ho))

/-- Every set of rank below an inaccessible `κ` has cardinality below `κ`. -/
theorem card_lt_of_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x.rank < κ.ord) : x.card < κ := by
  refine lt_of_le_of_lt (ZFSet.card_mono (ZFSet.subset_vonNeumann_self x)) ?_
  rw [ZFSet.card_vonNeumann]
  exact preBeth_lt_of_isInaccessible hκ _ hx

/-- The von Neumann naturals have finite rank. -/
theorem PSet_rank_ofNat_lt_omega0 (n : ℕ) : (PSet.ofNat n).rank < Ordinal.omega0 := by
  induction n with
  | zero => simp [PSet.ofNat, Ordinal.omega0_pos]
  | succ n ih =>
    rw [PSet.ofNat, PSet.rank_insert]
    exact max_lt (Order.IsSuccLimit.succ_lt Ordinal.isSuccLimit_omega0 ih) ih

/-- `ω` has rank at most `ω`. -/
theorem rank_omega_le : ZFSet.rank ZFSet.omega.{u} ≤ Ordinal.omega0.{u} := by
  rw [ZFSet.rank_le_iff]
  intro y hy
  induction y using Quotient.inductionOn with
  | _ p =>
    obtain ⟨i, hi⟩ := hy
    show PSet.rank p < Ordinal.omega0
    rw [PSet.rank_congr hi]
    exact PSet_rank_ofNat_lt_omega0 i.down

/-- For `κ` inaccessible, the sets of rank `< κ.ord` form a class satisfying the ZFC closure
conditions. -/
theorem isZFCClass_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    IsZFCClass (fun x : ZFSet.{u} => x.rank < κ.ord) := by
  have hlim : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_lt.le
  have homega : Ordinal.omega0.{u} < κ.ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.2 hκ.aleph0_lt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    exact (ZFSet.rank_lt_of_mem hy).trans hx
  · intro x y hx hy
    rw [ZFSet.rank_pair]
    exact max_lt (hlim.succ_lt hx) (hlim.succ_lt hy)
  · intro x hx
    exact (ZFSet.rank_sUnion_le x).trans_lt hx
  · intro x hx
    rw [ZFSet.rank_powerset]
    exact hlim.succ_lt hx
  · exact rank_omega_le.trans_lt homega
  · intro a f ha hf
    classical
    refine ⟨ZFSet.range (fun i : Shrink.{u} a => f ((equivShrink (α := (a : Type (u + 1)))).symm i)),
      ?_, ?_⟩
    · rw [ZFSet.rank_range]
      refine Cardinal.iSup_lt_ord_of_isRegular hκ.isRegular ?_ ?_
      · have : #(Shrink.{u} (a : Type (u + 1))) = a.card := rfl
        rw [this]
        exact card_lt_of_rank_lt hκ ha
      · intro i
        exact hlim.succ_lt (hf _ ((equivShrink (α := (a : Type (u + 1)))).symm i).2)
    · intro z
      rw [ZFSet.mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨_, ((equivShrink (α := (a : Type (u + 1)))).symm i).2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨equivShrink _ ⟨y, hy⟩, by simp⟩

/-- The same class, described as the level `V_ κ.ord` of the von Neumann hierarchy. -/
theorem isZFCClass_mem_vonNeumann {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    IsZFCClass (fun x : ZFSet.{u} => x ∈ ZFSet.vonNeumann κ.ord) := by
  have hfun : (fun x : ZFSet.{u} => x ∈ ZFSet.vonNeumann κ.ord)
      = fun x : ZFSet.{u} => x.rank < κ.ord :=
    funext fun x => propext ZFSet.mem_vonNeumann
  rw [hfun]
  exact isZFCClass_rank_lt hκ

end Frontier

/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.SetLanguage
import RequestProject.ZFCModel
import RequestProject.Inaccessible

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Summary

`Frontier.ZFC` is the theory of Zermelo–Fraenkel set theory with choice, written out in the
first-order language `Frontier.setLang` with a single binary relation symbol `∈`
(extensionality, foundation, pairing, union, power set, infinity, choice, and the separation
and replacement schemes, with one axiom for each first-order formula and each finite list of
parameters).

Consistency is taken in its semantic form: a theory is consistent when it has a model, i.e.
`FirstOrder.Language.Theory.IsSatisfiable`. (Mathlib has no deduction calculus for first-order
logic, so the completeness theorem is not available to relate this to the syntactic notion.)

The main theorem `Frontier.inaccessible_implies_ConZFC` says that from a strongly inaccessible
cardinal `κ` one obtains a model of ZFC, namely `V_κ`, the class of sets of rank `< κ.ord`;
hence `Con(ZFC)` holds. Combined with the trivial monotonicity of satisfiability
(`Frontier.ConZFC_of_isSatisfiable_extension`) this gives the reduction
`Con(ZFC + "there is an inaccessible") → Con(ZFC)`.
-/

open FirstOrder Language ZFSet

universe u v

namespace Frontier

/-- For `κ` inaccessible, the sets of rank `< κ.ord` (i.e. `V_κ`) form a model of ZFC. -/
theorem vonNeumann_models_ZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    VClass (fun x : ZFSet.{u} => x.rank < κ.ord) ⊨ ZFC.{u + 1} :=
  VClass.models_ZFC (isZFCClass_rank_lt hκ)

/-- The same model, described explicitly as the level `V_ κ.ord` of the von Neumann hierarchy. -/
theorem mem_vonNeumann_models_ZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    VClass (fun x : ZFSet.{u} => x ∈ ZFSet.vonNeumann κ.ord) ⊨ ZFC.{u + 1} :=
  VClass.models_ZFC (isZFCClass_mem_vonNeumann hκ)

/-- **An inaccessible cardinal yields a model of ZFC**, hence `Con(ZFC)`.

Here consistency is the semantic notion: `ZFC.IsSatisfiable` says that the first-order theory
`Frontier.ZFC` has a model. The model produced is `V_κ`, the class of sets of rank below
`κ.ord`, with the real membership relation. -/
theorem inaccessible_implies_ConZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    (ZFC.{u + 1}).IsSatisfiable := by
  have h := isZFCClass_rank_lt hκ
  haveI : Nonempty (VClass (fun x : ZFSet.{u} => x.rank < κ.ord)) :=
    ⟨⟨∅, h.empty⟩⟩
  haveI : VClass (fun x : ZFSet.{u} => x.rank < κ.ord) ⊨ ZFC.{u + 1} := vonNeumann_models_ZFC hκ
  exact Theory.Model.isSatisfiable (VClass (fun x : ZFSet.{u} => x.rank < κ.ord))

/-- `Con(ZFC + anything) → Con(ZFC)`: any consistent extension of ZFC witnesses the consistency
of ZFC.  In particular, taking `T` to be an axiom asserting the existence of an inaccessible
cardinal, `Con(ZFC + inaccessible) → Con(ZFC)`. -/
theorem ConZFC_of_isSatisfiable_extension {T : setLang.{u}.Theory}
    (h : (ZFC.{u} ∪ T).IsSatisfiable) : (ZFC.{u}).IsSatisfiable :=
  h.mono Set.subset_union_left

/-- The class of all sets is a model of ZFC, so `Con(ZFC)` is a theorem of Lean's type theory
outright (Lean's universe hierarchy provides inaccessible cardinals). The point of
`Frontier.inaccessible_implies_ConZFC` is that the model is built from a *given* inaccessible
cardinal, as `V_κ`. -/
theorem ConZFC : (ZFC.{u + 1}).IsSatisfiable := by
  haveI : Nonempty (VClass (fun _ : ZFSet.{u} => True)) := ⟨⟨∅, trivial⟩⟩
  haveI : VClass (fun _ : ZFSet.{u} => True) ⊨ ZFC.{u + 1} := VClass.models_ZFC isZFCClass_true
  exact Theory.Model.isSatisfiable (VClass (fun _ : ZFSet.{u} => True))

/-- A sanity check that the axiomatization is not degenerate: no one-element structure is a
model of `Frontier.ZFC` (the axiom of infinity already rules this out). -/
theorem not_models_ZFC_of_subsingleton {M : Type v} [setLang.{u}.Structure M] [Subsingleton M]
    [M ⊨ ZFC.{u}] : False := by
  have h : M ⊨ infAx.{u} := Theory.realize_sentence_of_mem ZFC (by
    simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto)
  rw [realize_infAx] at h
  obtain ⟨w, ⟨e, hew, he⟩, -⟩ := h
  rw [Subsingleton.elim w e] at hew
  exact he e hew

end Frontier

/-
The first-order language of set theory and the axioms of ZFC.
-/
import Mathlib

/-!
# The first-order language of set theory, and the theory ZFC

We define the first-order language `Frontier.setLang` with a single binary relation symbol `∈`,
and the theory `Frontier.ZFC` consisting of the usual axioms of Zermelo–Fraenkel set theory
with choice:

* extensionality, foundation (regularity), pairing, union, power set, infinity, choice
  (in Zermelo's "multiplicative axiom" form, which needs no coding of ordered pairs), and
* the separation and replacement schemes, one axiom for each first-order formula with
  finitely many parameters.

For each axiom we also prove a `realize_*` lemma unfolding what it means for a structure to
satisfy it.
-/

universe u w

namespace Frontier

open FirstOrder Language BoundedFormula

/-- The relation symbols of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/
def setLang.{v} : FirstOrder.Language.{v, v} :=
  ⟨fun _ => PEmpty, fun n => ULift (memRel n)⟩

/-- The membership relation symbol. -/
def memSymb : setLang.{u}.Relations 2 := ULift.up memRel.mem

@[inherit_doc] scoped notation:88 t₁ " ∈' " t₂ => Relations.boundedFormula₂ memSymb t₁ t₂

variable {M : Type w} [setLang.{u}.Structure M]

/-- The interpretation of the membership symbol in a structure. -/
def Mem' (x y : M) : Prop := Structure.RelMap (memSymb.{u}) ![x, y]

/-! ### The finitely many non-scheme axioms -/

/-- Extensionality: `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
def extAx : setLang.{u}.Sentence :=
  ∀' ∀' ((∀' ((&2 ∈' &0) ⇔ (&2 ∈' &1))) ⟹ (&0 =' &1))

/-- Foundation: every nonempty set has an `∈`-minimal element. -/
def foundAx : setLang.{u}.Sentence :=
  ∀' ((∃' (&1 ∈' &0)) ⟹ (∃' ((&1 ∈' &0) ⊓ (∼ (∃' ((&2 ∈' &1) ⊓ (&2 ∈' &0)))))))

/-- Pairing: `∀ x y, ∃ p, ∀ w, w ∈ p ↔ w = x ∨ w = y`. -/
def pairAx : setLang.{u}.Sentence :=
  ∀' ∀' ∃' ∀' ((&3 ∈' &2) ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))

/-- Union: `∀ a, ∃ u, ∀ z, z ∈ u ↔ ∃ y, z ∈ y ∧ y ∈ a`. -/
def unionAx : setLang.{u}.Sentence :=
  ∀' ∃' ∀' ((&2 ∈' &1) ⇔ (∃' ((&2 ∈' &3) ⊓ (&3 ∈' &0))))

/-- Power set: `∀ a, ∃ p, ∀ z, z ∈ p ↔ ∀ w, w ∈ z → w ∈ a`. -/
def powerAx : setLang.{u}.Sentence :=
  ∀' ∃' ∀' ((&2 ∈' &1) ⇔ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &0))))

/-- Infinity: there is a set containing an empty set and closed under `y ↦ y ∪ {y}`. -/
def infAx : setLang.{u}.Sentence :=
  ∃' ((∃' ((&1 ∈' &0) ⊓ (∀' (∼(&2 ∈' &1))))) ⊓
      (∀' ((&1 ∈' &0) ⟹
        (∃' ((&2 ∈' &0) ⊓ (∀' ((&3 ∈' &2) ⇔ ((&3 ∈' &1) ⊔ (&3 =' &1)))))))))

/-- Choice, in Zermelo's form: any family of nonempty, pairwise disjoint sets admits a
set meeting each member in exactly one point. -/
def choiceAx : setLang.{u}.Sentence :=
  ∀' (((∀' ((&1 ∈' &0) ⟹ (∃' (&2 ∈' &1)))) ⊓
       (∀' ∀' ((((&1 ∈' &0) ⊓ (&2 ∈' &0)) ⊓ (∃' ((&3 ∈' &1) ⊓ (&3 ∈' &2)))) ⟹ (&1 =' &2)))) ⟹
      (∃' (∀' ((&2 ∈' &0) ⟹
        (∃' (((&3 ∈' &2) ⊓ (&3 ∈' &1)) ⊓
          (∀' (((&4 ∈' &2) ⊓ (&4 ∈' &1)) ⟹ (&4 =' &3)))))))))

/-! ### The axiom schemes -/

/-- The instance of the separation scheme for a formula `φ` with `k` parameters and one
distinguished free variable: `∀ params, ∀ a, ∃ b, ∀ z, (z ∈ b ↔ z ∈ a ∧ φ z)`. -/
noncomputable def sepAx (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 1)) : setLang.{u}.Sentence :=
  Formula.iAlls (Fin k) (Formula.relabel Sum.inr
    (BoundedFormula.all (BoundedFormula.ex (BoundedFormula.all
      ((&2 ∈' &1) ⇔ ((&2 ∈' &0) ⊓
        (BoundedFormula.relabel
          (Sum.elim (fun p => Sum.inl p) (fun _ => Sum.inr 2) :
            Fin k ⊕ Fin 1 → Fin k ⊕ Fin 3) φ)))))))

/-- The instance of the replacement scheme for a formula `φ` with `k` parameters and two
distinguished free variables `x`, `y`: if `φ` is functional on `a`, then the image of `a`
under `φ` is a set. -/
noncomputable def replAx (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 2)) :
    setLang.{u}.Sentence :=
  Formula.iAlls (Fin k) (Formula.relabel Sum.inr
    (BoundedFormula.all
      ((BoundedFormula.all (BoundedFormula.all (BoundedFormula.all
        ((((&1 ∈' &0) ⊓
            (BoundedFormula.relabel
              (Sum.elim (fun p => Sum.inl p) (fun i => Sum.inr (if i = 0 then 1 else 2)) :
                Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ)) ⊓
            (BoundedFormula.relabel
              (Sum.elim (fun p => Sum.inl p) (fun i => Sum.inr (if i = 0 then 1 else 3)) :
                Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ)) ⟹ (&2 =' &3))))) ⟹
      (BoundedFormula.ex (BoundedFormula.all
        ((&2 ∈' &1) ⇔ (BoundedFormula.ex ((&3 ∈' &0) ⊓
          (BoundedFormula.relabel
            (Sum.elim (fun p => Sum.inl p) (fun i => Sum.inr (if i = 0 then 3 else 2)) :
              Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ)))))))))

/-- The theory ZFC in the first-order language of set theory. -/
noncomputable def ZFC : setLang.{u}.Theory :=
  {extAx, foundAx, pairAx, unionAx, powerAx, infAx, choiceAx} ∪
  {σ | ∃ (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 1)), σ = sepAx k φ} ∪
  {σ | ∃ (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 2)), σ = replAx k φ}

/-! ### Unfolding satisfaction of the axioms -/

theorem realize_extAx : M ⊨ extAx.{u} ↔ ∀ x y : M, (∀ z, Mem' z x ↔ Mem' z y) → x = y := by
  simp [extAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem']

theorem realize_foundAx : M ⊨ foundAx.{u} ↔
    ∀ x : M, (∃ y, Mem' y x) → ∃ y, Mem' y x ∧ ¬ ∃ z, Mem' z y ∧ Mem' z x := by
  simp [foundAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem']

theorem realize_pairAx : M ⊨ pairAx.{u} ↔
    ∀ x y : M, ∃ p, ∀ w, Mem' w p ↔ (w = x ∨ w = y) := by
  simp [pairAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem']

theorem realize_unionAx : M ⊨ unionAx.{u} ↔
    ∀ a : M, ∃ v, ∀ z, Mem' z v ↔ ∃ y, Mem' z y ∧ Mem' y a := by
  simp [unionAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem']

theorem realize_powerAx : M ⊨ powerAx.{u} ↔
    ∀ a : M, ∃ p, ∀ z, Mem' z p ↔ ∀ t, Mem' t z → Mem' t a := by
  simp [powerAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem']

theorem realize_infAx : M ⊨ infAx.{u} ↔
    ∃ v : M, (∃ e, Mem' e v ∧ ∀ z, ¬ Mem' z e) ∧
      ∀ y, Mem' y v → ∃ s, Mem' s v ∧ ∀ z, (Mem' z s ↔ (Mem' z y ∨ z = y)) := by
  simp [infAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem']

theorem realize_choiceAx : M ⊨ choiceAx.{u} ↔
    ∀ a : M, ((∀ x, Mem' x a → ∃ z, Mem' z x) ∧
        (∀ x x', ((Mem' x a ∧ Mem' x' a) ∧ ∃ z, Mem' z x ∧ Mem' z x') → x = x')) →
      ∃ c, ∀ x, Mem' x a → ∃ y, (Mem' y x ∧ Mem' y c) ∧
        ∀ y', (Mem' y' x ∧ Mem' y' c) → y' = y := by
  simp [choiceAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem']

/-- Two valuations agreeing pointwise realize the same formula. -/
theorem realize_congr_val {α : Type*} (φ : setLang.{u}.Formula α) {v v' : α → M}
    (h : ∀ a, v a = v' a) {xs xs' : Fin 0 → M} :
    BoundedFormula.Realize φ v xs ↔ BoundedFormula.Realize φ v' xs' :=
  iff_of_eq (congr (congrArg _ (funext h)) (Subsingleton.elim _ _))

theorem realize_sepAx (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 1)) :
    M ⊨ sepAx k φ ↔ ∀ (p : Fin k → M) (a : M), ∃ b : M, ∀ z : M,
      (Mem' z b ↔ Mem' z a ∧ φ.Realize (Sum.elim p (fun _ => z))) := by
  simp [sepAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem', Formula.relabel,
    Function.comp_def]
  refine forall_congr' fun i => forall_congr' fun a => exists_congr fun b => forall_congr' fun z =>
    iff_congr Iff.rfl (and_congr_right fun _ => ?_)
  exact realize_congr_val φ (by rintro (p | t) <;> simp [Fin.snoc])

theorem realize_replAx (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 2)) :
    M ⊨ replAx k φ ↔ ∀ (p : Fin k → M) (a : M),
      (∀ x y y' : M, ((Mem' x a ∧ φ.Realize (Sum.elim p ![x, y])) ∧
          φ.Realize (Sum.elim p ![x, y'])) → y = y') →
      ∃ b : M, ∀ y : M, (Mem' y b ↔ ∃ x, Mem' x a ∧ φ.Realize (Sum.elim p ![x, y])) := by
  simp [replAx, Sentence.Realize, Formula.Realize, Fin.snoc, Mem', Formula.relabel,
    Function.comp_def]
  refine forall_congr' fun i => forall_congr' fun a => imp_congr ?_ ?_
  · refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun y' =>
      imp_congr Iff.rfl (imp_congr ?_ (imp_congr ?_ Iff.rfl))
    · exact realize_congr_val φ (by rintro (p | t) <;> [skip; fin_cases t] <;> simp [Fin.snoc])
    · exact realize_congr_val φ (by rintro (p | t) <;> [skip; fin_cases t] <;> simp [Fin.snoc])
  · refine exists_congr fun b => forall_congr' fun y => iff_congr Iff.rfl
      (exists_congr fun x => and_congr_right fun _ => ?_)
    exact realize_congr_val φ (by rintro (p | t) <;> [skip; fin_cases t] <;> simp [Fin.snoc])

end Frontier

