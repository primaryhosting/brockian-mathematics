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
theorem preBeth_lt_of_lt_ord {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {a : Ordinal.{u}}
    (ha : a < κ.ord) : preBeth a < κ := by
  revert ha
  induction a using Ordinal.limitRecOn with
  | zero => intro _; simpa using hκ.pos
  | succ b ih =>
      intro hb
      rw [preBeth_succ]
      exact hκ.isStrongLimit.two_power_lt (ih ((lt_succ b).trans hb))
  | limit b hb ih =>
      intro hb'
      rw [preBeth_limit hb.isSuccPrelimit]
      have key : (⨆ a : Set.Iio b, preBeth (a : Ordinal.{u}))
          = ⨆ i : Shrink.{u} (Set.Iio b),
              preBeth (((equivShrink _).symm i : Set.Iio b) : Ordinal.{u}) := by
        apply le_antisymm
        · exact ciSup_le' fun x =>
            le_ciSup_of_le (Cardinal.bddAbove_of_small _) (equivShrink _ x) (by simp)
        · exact ciSup_le' fun i => le_ciSup (Cardinal.bddAbove_of_small _) _
      rw [key]
      apply Cardinal.iSup_lt_of_isRegular hκ.isRegular
      · have h1 : Cardinal.lift.{u + 1} #(Shrink.{u} (Set.Iio b))
            = Cardinal.lift.{u + 1} b.card := by
          rw [Cardinal.lift_mk_shrink'']
          exact mk_Iio_ordinal b
        rw [Cardinal.lift_injective h1]
        exact Cardinal.lt_ord.1 hb'
      · exact fun i => ih _ ((equivShrink _).symm i).2 (((equivShrink _).symm i).2.trans hb')

/-- Every element of `V_ κ.ord`, for `κ` inaccessible, has cardinality `< κ`. -/
theorem card_lt_of_mem_vonNeumann {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x ∈ V_ κ.ord) : x.card < κ := by
  have h1 : x.card ≤ (V_ x.rank).card := ZFSet.card_mono (ZFSet.subset_vonNeumann_self x)
  rw [ZFSet.card_vonNeumann] at h1
  exact h1.trans_lt (preBeth_lt_of_lt_ord hκ (ZFSet.mem_vonNeumann.1 hx))

/-- A family of ordinals `< κ.ord` indexed by (the elements of) a set in `V_ κ.ord` has
supremum `< κ.ord`; this is where regularity of `κ` is used. -/
theorem iSup_lt_ord_of_mem_vonNeumann {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {x : ZFSet.{u}} (hx : x ∈ V_ κ.ord) (f : Shrink.{u} x → Ordinal.{u})
    (hf : ∀ i, f i < κ.ord) : (⨆ i, f i) < κ.ord :=
  Cardinal.iSup_lt_ord_of_isRegular hκ.isRegular (card_lt_of_mem_vonNeumann hκ hx) hf

/-! ### `V_ κ` is a model of ZFC -/

/-- **An inaccessible cardinal yields a model of ZFC**: if `κ` is (strongly) inaccessible,
then the stage `V_ κ` of the cumulative hierarchy is a model of ZFC. -/
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
def setLang : Language := ⟨fun _ => Empty, memRel⟩

/-- The atomic formula `t₁ ∈ t₂`. -/
def memF {α : Type} {n : ℕ} (t₁ t₂ : setLang.Term (α ⊕ (Fin n))) :
    setLang.BoundedFormula α n :=
  Relations.boundedFormula memRel.mem ![t₁, t₂]

/-- Any ZFC set `M` is a `setLang`-structure, with `∈` interpreted as membership. -/
instance zfsetStructure (M : ZFSet.{u}) : setLang.Structure ↥M where
  funMap {_} f := Empty.elim f
  RelMap {n} r := match n, r with
    | 2, memRel.mem => fun v => ((v 0 : ↥M) : ZFSet.{u}) ∈ ((v 1 : ↥M) : ZFSet.{u})

@[simp] theorem realize_memF {M : ZFSet.{u}} {α : Type} {n : ℕ}
    (t₁ t₂ : setLang.Term (α ⊕ (Fin n))) (v : α → ↥M) (xs : Fin n → ↥M) :
    (memF t₁ t₂).Realize v xs ↔
      ((t₁.realize (Sum.elim v xs) : ↥M) : ZFSet.{u}) ∈
        ((t₂.realize (Sum.elim v xs) : ↥M) : ZFSet.{u}) := by
  simp [memF, BoundedFormula.Realize, Relations.boundedFormula, Structure.RelMap]

/-- Evaluation of a de Bruijn variable in a context extended by one element. -/
theorem snoc_mk {N : Type*} {m k : ℕ} (xs : Fin m → N) (a : N) (hk : k < m + 1) :
    (Fin.snoc xs a : Fin (m + 1) → N) ⟨k, hk⟩ = if h : k < m then xs ⟨k, h⟩ else a := by
  by_cases h : k < m
  · rw [dif_pos h, show (⟨k, hk⟩ : Fin (m + 1)) = (⟨k, h⟩ : Fin m).castSucc from rfl,
      Fin.snoc_castSucc]
  · rw [dif_neg h, show (⟨k, hk⟩ : Fin (m + 1)) = Fin.last m by
      simp only [Fin.ext_iff, Fin.val_last]; omega, Fin.snoc_last]

/-! ### The axioms of ZFC as first-order sentences -/

/-- Extensionality. -/
def extAx : setLang.Sentence :=
  ∀' ∀' ((∀' ((memF (&⟨2, by omega⟩) (&⟨0, by omega⟩)) ⇔
    (memF (&⟨2, by omega⟩) (&⟨1, by omega⟩)))) ⟹ (&⟨0, by omega⟩ =' &⟨1, by omega⟩))

/-- Existence of the empty set. -/
def emptyAx : setLang.Sentence :=
  ∃' ∀' (∼(memF (&⟨1, by omega⟩) (&⟨0, by omega⟩)))

/-- Pairing. -/
def pairAx : setLang.Sentence :=
  ∀' ∀' ∃' ∀' ((memF (&⟨3, by omega⟩) (&⟨2, by omega⟩)) ⇔
    ((&⟨3, by omega⟩ =' &⟨0, by omega⟩) ⊔ (&⟨3, by omega⟩ =' &⟨1, by omega⟩)))

/-- Union. -/
def unionAx : setLang.Sentence :=
  ∀' ∃' ∀' ((memF (&⟨2, by omega⟩) (&⟨1, by omega⟩)) ⇔
    (∃' ((memF (&⟨3, by omega⟩) (&⟨0, by omega⟩)) ⊓ (memF (&⟨2, by omega⟩) (&⟨3, by omega⟩)))))

/-- Power set. -/
def powerAx : setLang.Sentence :=
  ∀' ∃' ∀' ((memF (&⟨2, by omega⟩) (&⟨1, by omega⟩)) ⇔
    (∀' ((memF (&⟨3, by omega⟩) (&⟨2, by omega⟩)) ⟹ (memF (&⟨3, by omega⟩) (&⟨0, by omega⟩)))))

/-- Infinity. -/
def infAx : setLang.Sentence :=
  ∃' ((∃' ((memF (&⟨1, by omega⟩) (&⟨0, by omega⟩)) ⊓
      (∀' (∼(memF (&⟨2, by omega⟩) (&⟨1, by omega⟩)))))) ⊓
    (∀' ((memF (&⟨1, by omega⟩) (&⟨0, by omega⟩)) ⟹
      (∃' ((memF (&⟨2, by omega⟩) (&⟨0, by omega⟩)) ⊓
        (∀' ((memF (&⟨3, by omega⟩) (&⟨2, by omega⟩)) ⇔
          ((memF (&⟨3, by omega⟩) (&⟨1, by omega⟩)) ⊔ (&⟨3, by omega⟩ =' &⟨1, by omega⟩)))))))))

/-- Foundation. -/
def foundAx : setLang.Sentence :=
  ∀' ((∃' (memF (&⟨1, by omega⟩) (&⟨0, by omega⟩))) ⟹
    (∃' ((memF (&⟨1, by omega⟩) (&⟨0, by omega⟩)) ⊓
      (∀' ((memF (&⟨2, by omega⟩) (&⟨1, by omega⟩)) ⟹
        (∼(memF (&⟨2, by omega⟩) (&⟨0, by omega⟩))))))))

/-- The hypothesis of choice: every element of `x` (the variable `&0`) is nonempty. -/
def choiceHyp₁ : setLang.BoundedFormula Empty 1 :=
  ∀' ((memF (&⟨1, by omega⟩) (&⟨0, by omega⟩)) ⟹ (∃' (memF (&⟨2, by omega⟩) (&⟨1, by omega⟩))))

/-- The hypothesis of choice: the elements of `x` are pairwise disjoint. -/
def choiceHyp₂ : setLang.BoundedFormula Empty 1 :=
  ∀' (∀' ((memF (&⟨1, by omega⟩) (&⟨0, by omega⟩)) ⟹ ((memF (&⟨2, by omega⟩) (&⟨0, by omega⟩)) ⟹
    ((∼(&⟨1, by omega⟩ =' &⟨2, by omega⟩)) ⟹
      (∼(∃' ((memF (&⟨3, by omega⟩) (&⟨1, by omega⟩)) ⊓ (memF (&⟨3, by omega⟩) (&⟨2, by omega⟩)))))))))

/-- The conclusion of choice: there is a transversal for `x`. -/
def choiceConcl : setLang.BoundedFormula Empty 1 :=
  ∃' (∀' ((memF (&⟨2, by omega⟩) (&⟨0, by omega⟩)) ⟹
    (∃' (((memF (&⟨3, by omega⟩) (&⟨2, by omega⟩)) ⊓ (memF (&⟨3, by omega⟩) (&⟨1, by omega⟩))) ⊓
      (∀' (((memF (&⟨4, by omega⟩) (&⟨2, by omega⟩)) ⊓ (memF (&⟨4, by omega⟩) (&⟨1, by omega⟩))) ⟹
        (&⟨4, by omega⟩ =' &⟨3, by omega⟩)))))))

/-- Choice, in Zermelo's transversal form. -/
def choiceAx : setLang.Sentence :=
  ∀' (choiceHyp₁ ⟹ (choiceHyp₂ ⟹ choiceConcl))


def subVars {α β : Type} {m : ℕ} (g : α → β ⊕ Fin m) (fml : setLang.Formula α) :
    setLang.BoundedFormula β m :=
  BoundedFormula.relabel g fml

theorem realize_subVars {M : ZFSet.{u}} {α : Type} {m : ℕ} (g : α → Empty ⊕ Fin m)
    (fml : setLang.Formula α) (v : Empty → ↥M) (xs : Fin m → ↥M) :
    (subVars g fml).Realize v xs ↔ fml.Realize (Sum.elim v xs ∘ g) := by
  rw [subVars, BoundedFormula.realize_relabel]
  simp only [Formula.Realize, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id]
  rw [Subsingleton.elim (xs ∘ Fin.natAdd m) (default : Fin 0 → ↥M)]

def gSep (n : ℕ) : Fin (n+1) → Empty ⊕ Fin (n+3) :=
  fun i => if (i : ℕ) < n then Sum.inr (Fin.castLE (by omega) i) else Sum.inr ⟨n+2, by omega⟩

theorem valSep {M : ZFSet.{u}} {n : ℕ} (xs : Fin n → ↥M) (x s z : ↥M) :
    Sum.elim (default : Empty → ↥M)
        (Fin.snoc (Fin.snoc (Fin.snoc xs x) s) z : Fin (n+3) → ↥M) ∘ gSep n
      = Fin.snoc xs z := by
  funext i
  obtain ⟨k, hk⟩ := i
  by_cases hkn : k < n
  · have h1 : k < n + 2 := by omega
    have h2 : k < n + 1 := by omega
    simp [gSep, snoc_mk, hkn, h1, h2]
  · simp [gSep, snoc_mk, hkn]

def sepAx (n : ℕ) (fml : setLang.Formula (Fin (n+1))) : setLang.Sentence :=
  (∀' ∃' ∀' ((memF (&⟨n+2, by omega⟩) (&⟨n+1, by omega⟩)) ⇔
      ((memF (&⟨n+2, by omega⟩) (&⟨n, by omega⟩)) ⊓ (subVars (gSep n) fml)))).alls


def gRep (n : ℕ) (ia ib : ℕ) (hia : ia < n+4) (hib : ib < n+4) :
    Fin (n+2) → Empty ⊕ Fin (n+4) :=
  fun i => if (i : ℕ) < n then Sum.inr (Fin.castLE (by omega) i)
    else if (i : ℕ) = n then Sum.inr ⟨ia, hia⟩ else Sum.inr ⟨ib, hib⟩

def gRep₁ (n : ℕ) : Fin (n+2) → Empty ⊕ Fin (n+4) :=
  gRep n (n+1) (n+2) (by omega) (by omega)

def gRep₂ (n : ℕ) : Fin (n+2) → Empty ⊕ Fin (n+4) :=
  gRep n (n+1) (n+3) (by omega) (by omega)

def gRep₃ (n : ℕ) : Fin (n+2) → Empty ⊕ Fin (n+4) :=
  gRep n (n+3) (n+2) (by omega) (by omega)

section

variable {M : ZFSet.{u}}

theorem valRep₁ {n : ℕ} (xs : Fin n → ↥M) (c₁ c₂ c₃ c₄ : ↥M) :
    Sum.elim (default : Empty → ↥M)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs c₁) c₂) c₃) c₄ : Fin (n+4) → ↥M) ∘ gRep₁ n
      = Fin.snoc (Fin.snoc xs c₂) c₃ := by
  funext i
  obtain ⟨k, hk⟩ := i
  rcases lt_trichotomy k n with hkn | hkn | hkn
  · have h1 : k < n + 3 := by omega
    have h2 : k < n + 2 := by omega
    have h3 : k < n + 1 := by omega
    simp [gRep₁, gRep, snoc_mk, hkn, h1, h2, h3]
  · subst hkn
    simp [gRep₁, gRep, snoc_mk]
  · have hkn' : k = n + 1 := by omega
    subst hkn'
    simp [gRep₁, gRep, snoc_mk]

theorem valRep₂ {n : ℕ} (xs : Fin n → ↥M) (c₁ c₂ c₃ c₄ : ↥M) :
    Sum.elim (default : Empty → ↥M)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs c₁) c₂) c₃) c₄ : Fin (n+4) → ↥M) ∘ gRep₂ n
      = Fin.snoc (Fin.snoc xs c₂) c₄ := by
  funext i
  obtain ⟨k, hk⟩ := i
  rcases lt_trichotomy k n with hkn | hkn | hkn
  · have h1 : k < n + 3 := by omega
    have h2 : k < n + 2 := by omega
    have h3 : k < n + 1 := by omega
    simp [gRep₂, gRep, snoc_mk, hkn, h1, h2, h3]
  · subst hkn
    simp [gRep₂, gRep, snoc_mk]
  · have hkn' : k = n + 1 := by omega
    subst hkn'
    simp [gRep₂, gRep, snoc_mk]

theorem valRep₃ {n : ℕ} (xs : Fin n → ↥M) (c₁ c₂ c₃ c₄ : ↥M) :
    Sum.elim (default : Empty → ↥M)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs c₁) c₂) c₃) c₄ : Fin (n+4) → ↥M) ∘ gRep₃ n
      = Fin.snoc (Fin.snoc xs c₄) c₃ := by
  funext i
  obtain ⟨k, hk⟩ := i
  rcases lt_trichotomy k n with hkn | hkn | hkn
  · have h1 : k < n + 3 := by omega
    have h2 : k < n + 2 := by omega
    have h3 : k < n + 1 := by omega
    simp [gRep₃, gRep, snoc_mk, hkn, h1, h2, h3]
  · subst hkn
    simp [gRep₃, gRep, snoc_mk]
  · have hkn' : k = n + 1 := by omega
    subst hkn'
    simp [gRep₃, gRep, snoc_mk]

end

/-- The replacement scheme. -/
def replAx (n : ℕ) (fml : setLang.Formula (Fin (n+2))) : setLang.Sentence :=
  (∀' (((∀' ∀' ∀' ((((memF (&⟨n+1, by omega⟩) (&⟨n, by omega⟩)) ⊓
          ((subVars (gRep₁ n) fml) ⊓ (subVars (gRep₂ n) fml)))) ⟹
        (&⟨n+2, by omega⟩ =' &⟨n+3, by omega⟩)))) ⟹
    (∃' (∀' ((memF (&⟨n+2, by omega⟩) (&⟨n+1, by omega⟩)) ⇔
      (∃' ((memF (&⟨n+3, by omega⟩) (&⟨n, by omega⟩)) ⊓ (subVars (gRep₃ n) fml)))))))).alls

/-! ### The sentences express exactly the relativized ZFC axioms -/

section Meaning

variable {M : ZFSet.{u}}

theorem models_extAx_iff : (↥M ⊨ extAx) ↔
    ∀ x ∈ M, ∀ y ∈ M, (∀ z ∈ M, z ∈ x ↔ z ∈ y) → x = y := by
  simp only [extAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual,
    realize_memF, Term.realize_var, Function.comp_apply, Sum.elim_inr, snoc_mk]
  norm_num

theorem models_emptyAx_iff : (↥M ⊨ emptyAx) ↔ ∃ e ∈ M, ∀ z ∈ M, z ∉ e := by
  simp only [emptyAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, realize_memF, Term.realize_var,
    Function.comp_apply, Sum.elim_inr, snoc_mk]
  norm_num

theorem models_pairAx_iff : (↥M ⊨ pairAx) ↔
    ∀ x ∈ M, ∀ y ∈ M, ∃ p ∈ M, ∀ z ∈ M, (z ∈ p ↔ z = x ∨ z = y) := by
  simp only [pairAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_sup,
    BoundedFormula.realize_bdEqual, realize_memF, Term.realize_var,
    Function.comp_apply, Sum.elim_inr, snoc_mk]
  norm_num

theorem models_unionAx_iff : (↥M ⊨ unionAx) ↔
    ∀ x ∈ M, ∃ u ∈ M, ∀ z ∈ M, (z ∈ u ↔ ∃ y ∈ M, y ∈ x ∧ z ∈ y) := by
  simp only [unionAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_inf,
    realize_memF, Term.realize_var, Function.comp_apply, Sum.elim_inr, snoc_mk]
  norm_num
  constructor
  · intro H x hx
    obtain ⟨u, huM, hu⟩ := H x hx
    exact ⟨u, huM, fun z hz => (hu z hz).trans ⟨fun ⟨y, hyx, hyM, h2⟩ => ⟨y, hyM, hyx, h2⟩,
      fun ⟨y, hyM, hyx, h2⟩ => ⟨y, hyx, hyM, h2⟩⟩⟩
  · intro H x hx
    obtain ⟨u, huM, hu⟩ := H x hx
    exact ⟨u, huM, fun z hz => (hu z hz).trans ⟨fun ⟨y, hyM, hyx, h2⟩ => ⟨y, hyx, hyM, h2⟩,
      fun ⟨y, hyx, hyM, h2⟩ => ⟨y, hyM, hyx, h2⟩⟩⟩

theorem models_powerAx_iff : (↥M ⊨ powerAx) ↔
    ∀ x ∈ M, ∃ p ∈ M, ∀ z ∈ M, (z ∈ p ↔ ∀ w ∈ M, w ∈ z → w ∈ x) := by
  simp only [powerAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_imp,
    realize_memF, Term.realize_var, Function.comp_apply, Sum.elim_inr, snoc_mk]
  norm_num

theorem models_infAx_iff : (↥M ⊨ infAx) ↔
    ∃ i ∈ M, (∃ e ∈ M, e ∈ i ∧ ∀ z ∈ M, z ∉ e) ∧
      ∀ x ∈ M, x ∈ i → ∃ y ∈ M, y ∈ i ∧ ∀ z ∈ M, (z ∈ y ↔ z ∈ x ∨ z = x) := by
  simp only [infAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_sup, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, realize_memF, Term.realize_var, Function.comp_apply,
    Sum.elim_inr, snoc_mk]
  norm_num
  constructor
  · rintro ⟨i, ⟨e, hei, heM, he⟩, hiM, hsucc⟩
    refine ⟨i, hiM, ⟨e, heM, hei, he⟩, fun x hxM hxi => ?_⟩
    obtain ⟨y, hyi, hyM, hy⟩ := hsucc x hxM hxi
    exact ⟨y, hyM, hyi, hy⟩
  · rintro ⟨i, hiM, ⟨e, heM, hei, he⟩, hsucc⟩
    refine ⟨i, ⟨e, hei, heM, he⟩, hiM, fun x hxM hxi => ?_⟩
    obtain ⟨y, hyM, hyi, hy⟩ := hsucc x hxM hxi
    exact ⟨y, hyi, hyM, hy⟩

theorem models_foundAx_iff : (↥M ⊨ foundAx) ↔
    ∀ x ∈ M, (∃ z ∈ M, z ∈ x) → ∃ y ∈ M, y ∈ x ∧ ∀ z ∈ M, z ∈ y → z ∉ x := by
  simp only [foundAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, realize_memF, Term.realize_var, Function.comp_apply,
    Sum.elim_inr, snoc_mk]
  norm_num
  constructor
  · intro H x hx z hzM hzx
    obtain ⟨y, hyx, hyM, hy⟩ := H x hx z hzM hzx
    exact ⟨y, hyM, hyx, hy⟩
  · intro H x hx z hzM hzx
    obtain ⟨y, hyM, hyx, hy⟩ := H x hx z hzM hzx
    exact ⟨y, hyx, hyM, hy⟩

theorem models_choiceAx_iff : (↥M ⊨ choiceAx) ↔
    ∀ x ∈ M, (∀ y ∈ M, y ∈ x → ∃ z ∈ M, z ∈ y) →
      (∀ y ∈ M, ∀ y' ∈ M, y ∈ x → y' ∈ x → y ≠ y' → ¬ ∃ z ∈ M, z ∈ y ∧ z ∈ y') →
      ∃ c ∈ M, ∀ y ∈ M, y ∈ x → ∃! z, z ∈ M ∧ z ∈ y ∧ z ∈ c := by
  simp only [choiceAx, choiceHyp₁, choiceHyp₂, choiceConcl, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    realize_memF, Term.realize_var, Function.comp_apply, Sum.elim_inr, snoc_mk]
  norm_num
  constructor
  · intro H x hx hne hdisj
    obtain ⟨c, hcM, hc⟩ := H x hx hne
      (fun y hyM y' hy'M hyx hy'x hyy' z hzy hzM => hdisj y hyM y' hy'M hyx hy'x hyy' z hzM hzy)
    refine ⟨c, hcM, fun y hyM hyx => ?_⟩
    obtain ⟨z, ⟨hzy, hzc⟩, hzM, huniq⟩ := hc y hyM hyx
    exact ⟨z, ⟨hzM, hzy, hzc⟩, fun w hw => huniq w hw.1 hw.2.1 hw.2.2⟩
  · intro H x hx hne hdisj
    obtain ⟨c, hcM, hc⟩ := H x hx hne
      (fun y hyM y' hy'M hyx hy'x hyy' z hzM hzy => hdisj y hyM y' hy'M hyx hy'x hyy' z hzy hzM)
    refine ⟨c, hcM, fun y hyM hyx => ?_⟩
    obtain ⟨z, ⟨hzM, hzy, hzc⟩, huniq⟩ := hc y hyM hyx
    exact ⟨z, ⟨hzy, hzc⟩, hzM, fun w hwM hwy hwc => huniq w ⟨hwM, hwy, hwc⟩⟩

theorem models_sepAx_iff (n : ℕ) (fml : setLang.Formula (Fin (n+1))) :
    (↥M ⊨ sepAx n fml) ↔ ∀ (xs : Fin n → ↥M) (x : ↥M), ∃ s : ↥M, ∀ z : ↥M,
      ((z : ZFSet.{u}) ∈ (s : ZFSet.{u}) ↔
        (z : ZFSet.{u}) ∈ (x : ZFSet.{u}) ∧ fml.Realize (Fin.snoc xs z)) := by
  simp only [sepAx, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_inf,
    realize_memF, Term.realize_var, Function.comp_apply, Sum.elim_inr, snoc_mk, realize_subVars,
    valSep]
  norm_num

theorem models_replAx_iff (n : ℕ) (fml : setLang.Formula (Fin (n+2))) :
    (↥M ⊨ replAx n fml) ↔ ∀ (xs : Fin n → ↥M) (x : ↥M),
      (∀ a b b' : ↥M, (a : ZFSet.{u}) ∈ (x : ZFSet.{u}) →
          fml.Realize (Fin.snoc (Fin.snoc xs a) b) →
          fml.Realize (Fin.snoc (Fin.snoc xs a) b') → b = b') →
        ∃ r : ↥M, ∀ b : ↥M, ((b : ZFSet.{u}) ∈ (r : ZFSet.{u}) ↔
          ∃ a : ↥M, (a : ZFSet.{u}) ∈ (x : ZFSet.{u}) ∧
            fml.Realize (Fin.snoc (Fin.snoc xs a) b)) := by
  simp only [replAx, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual, realize_memF, Term.realize_var,
    Function.comp_apply, Sum.elim_inr, snoc_mk, realize_subVars, valRep₁, valRep₂, valRep₃]
  norm_num

end Meaning

/-! ### A model of `IsZFCModel` satisfies all the first-order axioms -/

section Realize

variable {M : ZFSet.{u}} (h : IsZFCModel M)

include h

theorem realize_extAx : (↥M ⊨ extAx) := models_extAx_iff.2 h.ext

theorem realize_emptyAx : (↥M ⊨ emptyAx) := models_emptyAx_iff.2 h.empty

theorem realize_pairAx : (↥M ⊨ pairAx) := models_pairAx_iff.2 h.pairing

theorem realize_unionAx : (↥M ⊨ unionAx) := models_unionAx_iff.2 h.union

theorem realize_powerAx : (↥M ⊨ powerAx) := models_powerAx_iff.2 h.powerset

theorem realize_infAx : (↥M ⊨ infAx) := models_infAx_iff.2 h.infinity

theorem realize_foundAx : (↥M ⊨ foundAx) := models_foundAx_iff.2 h.foundation

theorem realize_choiceAx : (↥M ⊨ choiceAx) := models_choiceAx_iff.2 h.choice

theorem realize_sepAx (n : ℕ) (fml : setLang.Formula (Fin (n+1))) : (↥M ⊨ sepAx n fml) := by
  refine models_sepAx_iff n fml |>.2 fun xs x => ?_
  obtain ⟨s, hsM, hs⟩ := h.separation
    (fun w => ∀ hw : w ∈ M, fml.Realize (Fin.snoc xs ⟨w, hw⟩)) x x.2
  exact ⟨⟨s, hsM⟩, fun z => (hs z z.2).trans
    (and_congr_right fun _ => ⟨fun hp => hp z.2, fun hp _ => hp⟩)⟩

/-- Replacement for an arbitrary binary relation which is functional on `M`: the image of a
set `x ∈ M` is again an element of `M`.  (No totality is assumed: elements of `x` outside the
domain of `R` are simply skipped.) -/
theorem exists_image (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hRmem : ∀ w v, R w v → w ∈ M ∧ v ∈ M)
    (hfun : ∀ a b b', R a b → R a b' → b = b') (x : ZFSet.{u}) (hx : x ∈ M) :
    ∃ r ∈ M, ∀ z ∈ M, (z ∈ r ↔ ∃ a ∈ x, R a z) := by
  classical
  obtain ⟨x', hx'M, hx'⟩ := h.separation (fun w => ∃ v, R w v) x hx
  refine ?_
  set F : ZFSet.{u} → ZFSet.{u} := fun w => if hw : ∃ v, R w v then hw.choose else ∅ with hF
  have hFspec : ∀ w, ∀ hw : ∃ v, R w v, R w (F w) := by
    intro w hw
    rw [hF]
    simp only [dif_pos hw]
    exact hw.choose_spec
  have hFmem : ∀ a ∈ M, a ∈ x' → F a ∈ M := by
    intro a haM hax'
    obtain ⟨-, hex⟩ := (hx' a haM).1 hax'
    exact (hRmem _ _ (hFspec a hex)).2
  obtain ⟨r, hrM, hr⟩ := h.replacement F x' hx'M hFmem
  refine ⟨r, hrM, fun z hz => ?_⟩
  rw [hr z hz]
  constructor
  · rintro ⟨a, haM, hax', rfl⟩
    obtain ⟨hax, hex⟩ := (hx' a haM).1 hax'
    exact ⟨a, hax, hFspec a hex⟩
  · rintro ⟨a, hax, hRaz⟩
    have haM : a ∈ M := (hRmem _ _ hRaz).1
    have hex : ∃ v, R a v := ⟨z, hRaz⟩
    have hax' : a ∈ x' := (hx' a haM).2 ⟨hax, hex⟩
    exact ⟨a, haM, hax', hfun a (F a) z (hFspec a hex) hRaz⟩

theorem realize_replAx (n : ℕ) (fml : setLang.Formula (Fin (n+2))) :
    (↥M ⊨ replAx n fml) := by
  refine models_replAx_iff n fml |>.2 fun xs x hfun => ?_
  obtain ⟨r, hrM, hr⟩ := exists_image h
    (fun w v => ∃ (_ : w ∈ (x : ZFSet.{u})) (hw : w ∈ M) (hv : v ∈ M),
      fml.Realize (Fin.snoc (Fin.snoc xs ⟨w, hw⟩) ⟨v, hv⟩))
    (fun _ _ hwv => ⟨hwv.choose_spec.choose, hwv.choose_spec.choose_spec.choose⟩)
    (fun a b b' hb hb' => by
      obtain ⟨hax, haM, hbM, hbreal⟩ := hb
      obtain ⟨hax2, haM2, hbM2, hbreal2⟩ := hb'
      exact congrArg Subtype.val
        (hfun ⟨a, haM⟩ ⟨b, hbM⟩ ⟨b', hbM2⟩ hax hbreal hbreal2))
    x x.2
  refine ⟨⟨r, hrM⟩, fun b => (hr b b.2).trans ⟨?_, ?_⟩⟩
  · rintro ⟨a, hax, -, haM, hbM, hreal⟩
    exact ⟨⟨a, haM⟩, hax, hreal⟩
  · rintro ⟨a, hax, hreal⟩
    exact ⟨a, hax, hax, a.2, b.2, hreal⟩

end Realize

/-! ### The first-order theory ZFC and its satisfiability -/

/-- The first-order theory ZFC: the eight finitely many axioms together with all instances of
the separation and replacement schemes. -/
def ZFCTheory : setLang.Theory :=
  ({extAx, emptyAx, pairAx, unionAx, powerAx, infAx, foundAx, choiceAx} ∪
    {sen | ∃ (n : ℕ) (fml : setLang.Formula (Fin (n + 1))), sen = sepAx n fml}) ∪
    {sen | ∃ (n : ℕ) (fml : setLang.Formula (Fin (n + 2))), sen = replAx n fml}

/-- Any model of ZFC in the sense of `IsZFCModel` is a model of the first-order theory
`ZFCTheory`. -/
theorem model_ZFCTheory {M : ZFSet.{u}} (h : IsZFCModel M) : ↥M ⊨ ZFCTheory := by
  rw [Theory.model_iff]
  intro sen hsen
  simp only [ZFCTheory, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq] at hsen
  rcases hsen with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨n, fml, rfl⟩) | ⟨n, fml, rfl⟩
  · exact realize_extAx h
  · exact realize_emptyAx h
  · exact realize_pairAx h
  · exact realize_unionAx h
  · exact realize_powerAx h
  · exact realize_infAx h
  · exact realize_foundAx h
  · exact realize_choiceAx h
  · exact realize_sepAx h n fml
  · exact realize_replAx h n fml

/-- `ConZFC` is the (semantic) consistency of ZFC: the first-order theory `ZFCTheory` has a
model. -/
def ConZFC : Prop := ZFCTheory.IsSatisfiable

/-- A model of ZFC in the sense of `IsZFCModel` witnesses the consistency of the first-order
theory ZFC. -/
theorem conZFC_of_isZFCModel {M : ZFSet.{u}} (h : IsZFCModel M) : ConZFC := by
  obtain ⟨x, hx⟩ := h.nonempty
  haveI : Nonempty ↥M := ⟨⟨x, hx⟩⟩
  haveI : ↥M ⊨ ZFCTheory := model_ZFCTheory h
  exact Theory.Model.isSatisfiable ↥M

/-- **Inaccessible implies Con(ZFC)**: the existence of an inaccessible cardinal yields a
model of ZFC, hence the (semantic) consistency of the first-order theory ZFC. Consequently
`Con(ZFC + "there is an inaccessible cardinal") → Con(ZFC)`: any model of
`ZFC + "there is an inaccessible cardinal"` contains an inaccessible cardinal and therefore
builds a model of ZFC. -/
theorem inaccessible_implies_ConZFC (h : ∃ κ : Cardinal.{u}, κ.IsInaccessible) : ConZFC :=
  let ⟨_, hκ⟩ := h
  conZFC_of_isZFCModel (isZFCModel_vonNeumann_ord hκ)

end Frontier

