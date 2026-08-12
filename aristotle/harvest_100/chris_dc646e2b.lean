/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes the statement that a (strongly) inaccessible cardinal `κ` yields a model of
`ZFC`, namely the rank-initial segment `V κ = {x : ZFSet | rank x < κ.ord}` of the von Neumann
hierarchy, and deduces the semantic consistency statement `Con(ZFC)` (i.e. satisfiability of the
first-order theory `ZFCTheory`) from the existence of an inaccessible cardinal.
-/

universe u

namespace Frontier

open FirstOrder Language Cardinal Ordinal ZFSet

/-! ## The first-order language of set theory -/

/-- The relations of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The first-order language of set theory: one binary relation symbol, no functions. -/
def setLang : Language := ⟨fun _ => Empty, memRel⟩

/-- The membership relation symbol. -/
abbrev memSymb : setLang.Relations 2 := memRel.mem

/-- The atomic formula `t ∈ u`. -/
abbrev memf {n : ℕ} (t u : setLang.Term (Empty ⊕ Fin n)) : setLang.BoundedFormula Empty n :=
  memSymb.boundedFormula₂ t u

/-! ## The axioms of ZFC -/

/-- Extensionality. -/
def extAx : setLang.Sentence :=
  ∀' ∀' ((∀' (memf &2 &0 ⇔ memf &2 &1)) ⟹ (&0 =' &1))

/-- Foundation (regularity). -/
def foundAx : setLang.Sentence :=
  ∀' ((∃' (memf &1 &0)) ⟹ ∃' ((memf &1 &0) ⊓ ∼(∃' ((memf &2 &1) ⊓ (memf &2 &0)))))

/-- Pairing. -/
def pairAx : setLang.Sentence :=
  ∀' ∀' ∃' ∀' ((memf &3 &2) ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))

/-- Union. -/
def unionAx : setLang.Sentence :=
  ∀' ∃' ∀' ((memf &2 &1) ⇔ ∃' ((memf &3 &0) ⊓ (memf &2 &3)))

/-- Power set. -/
def powerAx : setLang.Sentence :=
  ∀' ∃' ∀' ((memf &2 &1) ⇔ ∀' ((memf &3 &2) ⟹ (memf &3 &0)))

/-- Infinity: there is a set containing `∅` and closed under `x ↦ x ∪ {x}`. -/
def infAx : setLang.Sentence :=
  ∃' (((∃' ((memf &1 &0) ⊓ ∀' ∼(memf &2 &1)))) ⊓
    ∀' ((memf &1 &0) ⟹ ∃' ((memf &2 &0) ⊓
      ∀' ((memf &3 &2) ⇔ ((memf &3 &1) ⊔ (&3 =' &1))))))

/-- The axiom of choice, in the form: every set of pairwise disjoint nonempty sets admits a
transversal. -/
def acAx : setLang.Sentence :=
  ∀' (((∀' ((memf &1 &0) ⟹ ∃' (memf &2 &1))) ⊓
        (∀' ∀' ((((memf &1 &0) ⊓ (memf &2 &0)) ⊓ ∼(&1 =' &2)) ⟹
          ∼(∃' ((memf &3 &1) ⊓ (memf &3 &2)))))) ⟹
    ∃' (∀' ((memf &2 &0) ⟹
      ∃' (((memf &3 &2) ⊓ (memf &3 &1)) ⊓
        ∀' (((memf &4 &2) ⊓ (memf &4 &1)) ⟹ (&4 =' &3))))))

section Schemas

variable {n : ℕ}

/-- The separation (subset) schema, for a formula `φ` whose free variables are `n` parameters
together with the variable being separated. -/
def sepAx (φ : setLang.BoundedFormula Empty (n + 1)) : setLang.Sentence :=
  (∀' ∃' ∀' ((memf (&(Fin.last (n + 2))) (&((Fin.last (n + 1)).castSucc))) ⇔
    ((memf (&(Fin.last (n + 2))) (&(((Fin.last n).castSucc).castSucc))) ⊓ φ.liftAt 2 n))).alls

/-- The collection schema, for a formula `φ` whose free variables are `n` parameters together with
two further variables `x`, `y`. Together with separation this yields the replacement schema. -/
def collAx (φ : setLang.BoundedFormula Empty (n + 2)) : setLang.Sentence :=
  (∀' ((∀' ((memf (&(Fin.last (n + 1))) (&((Fin.last n).castSucc))) ⟹
      ∃' (φ.liftAt 1 n))) ⟹
    ∃' ∀' ((memf (&(Fin.last (n + 2))) (&(((Fin.last n).castSucc).castSucc))) ⟹
      ∃' (((memf (&(Fin.last (n + 3))) (&(((Fin.last (n + 1)).castSucc).castSucc)))) ⊓
        φ.liftAt 2 n)))).alls

end Schemas

/-- The first-order theory ZFC: extensionality, foundation, pairing, union, power set, infinity,
choice, together with the separation and collection schemas. (Separation and collection together
are deductively equivalent to the usual separation and replacement schemas.) -/
def ZFCTheory : setLang.Theory :=
  {extAx, foundAx, pairAx, unionAx, powerAx, infAx, acAx}
    ∪ (Set.range fun p : (Σ n : ℕ, setLang.BoundedFormula Empty (n + 1)) => sepAx p.2)
    ∪ (Set.range fun p : (Σ n : ℕ, setLang.BoundedFormula Empty (n + 2)) => collAx p.2)

/-! ## The model `V κ` -/

/-- The rank-initial segment of the von Neumann hierarchy below `κ.ord`. -/
abbrev Vs (κ : Cardinal.{u}) : Type (u + 1) := {x : ZFSet.{u} // x.rank < κ.ord}

instance instStructureVs (κ : Cardinal.{u}) : setLang.Structure (Vs κ) where
  funMap {_} f := (f : Empty).elim
  RelMap {n} r := match n, r with
    | 2, memRel.mem => fun x => (x 0).1 ∈ (x 1).1

/-! ### Closure properties of `V κ` -/

section Closure

variable {κ : Cardinal.{u}}

/-- For `o < κ.ord` with `κ` inaccessible, there are fewer than `κ` sets of rank `< o`. -/
theorem mk_rank_lt_lt (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → #{x : ZFSet.{u} // x.rank < o} < Cardinal.lift.{u+1,u} κ := by
  intro o
  induction o using Ordinal.induction with
  | _ o IH =>
  intro ho
  have hset : {x : ZFSet.{u} | x.rank < o}
      = ⋃ (i : o.ToType), {x : ZFSet.{u} | x.rank = (ToType.toOrd i : Ordinal)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hx
      exact ⟨ToType.mk ⟨x.rank, hx⟩, by simp [ToType.toOrd]⟩
    · rintro ⟨i, hi⟩
      rw [hi]
      exact (ToType.toOrd i).2
  have hstep : ∀ b : Ordinal.{u},
      #{x : ZFSet.{u} | x.rank = b} ≤ 2 ^ #{y : ZFSet.{u} | y.rank < b} := by
    intro b
    rw [← Cardinal.mk_set]
    apply Cardinal.mk_le_of_injective (f := fun x => {y : {y : ZFSet.{u} | y.rank < b} | y.1 ∈ x.1})
    intro x y h
    simp only [Set.ext_iff, Set.mem_setOf_eq, Subtype.forall] at h
    refine Subtype.ext (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · exact (h z (x.2 ▸ ZFSet.rank_lt_of_mem hz)).1 hz
    · exact (h z (y.2 ▸ ZFSet.rank_lt_of_mem hz)).2 hz
  have hreg : (Cardinal.lift.{u+1,u} κ).IsRegular := hκ.isRegular.lift
  have hcard : Cardinal.lift.{u+1,u} #(o.ToType) < Cardinal.lift.{u+1,u} κ := by
    rw [Cardinal.lift_lt, Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp ho
  have hsum : (Cardinal.sum fun i : o.ToType =>
        #{x : ZFSet.{u} | x.rank = (ToType.toOrd i : Ordinal)}) < Cardinal.lift.{u+1,u} κ := by
    refine Cardinal.sum_lt_lift_of_isRegular hreg hcard fun i => ?_
    refine lt_of_le_of_lt (hstep _) ?_
    have hlt : #{y : ZFSet.{u} | y.rank < (ToType.toOrd i : Ordinal)} < Cardinal.lift.{u+1,u} κ :=
      IH _ (ToType.toOrd i).2 (((ToType.toOrd i).2).trans ho)
    obtain ⟨A, hAlt, hA⟩ := Cardinal.lt_lift_iff.mp hlt
    rw [← hA, ← Cardinal.lift_two_power, Cardinal.lift_lt]
    exact hκ.isStrongLimit.two_power_lt hAlt
  have heq : #{x : ZFSet.{u} // x.rank < o} = #({x : ZFSet.{u} | x.rank < o} : Set ZFSet.{u}) := rfl
  rw [heq, hset]
  have hle := @Cardinal.mk_iUnion_le_sum_mk_lift ZFSet.{u} o.ToType
      (fun i => {x : ZFSet.{u} | x.rank = (ToType.toOrd i : Ordinal)})
  rw [Cardinal.lift_id'.{u, u+1}] at hle
  exact lt_of_le_of_lt hle hsum

/-- A set in `V κ` has fewer than `κ` elements. -/
theorem mk_shrink_lt (hκ : κ.IsInaccessible) (a : ZFSet.{u}) (ha : a.rank < κ.ord) :
    #(Shrink.{u} ↥a) < κ := by
  have h1 : #(↥a) ≤ #{x : ZFSet.{u} // x.rank < a.rank} := by
    apply Cardinal.mk_le_of_injective
      (f := fun z : ↥a => (⟨z.1, ZFSet.rank_lt_of_mem z.2⟩ : {x : ZFSet.{u} // x.rank < a.rank}))
    intro x y h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have h2 := lt_of_le_of_lt h1 (mk_rank_lt_lt hκ a.rank ha)
  have h3 : Cardinal.lift.{u+1,u} #(Shrink.{u} ↥a) = #(↥a) := by
    rw [Cardinal.lift_mk_shrink']
    exact Cardinal.lift_id'.{u, u+1} _
  rw [← h3] at h2
  exact Cardinal.lift_lt.mp h2

/-- The range of a family indexed by (the elements of) a set of `V κ` lies in `V κ`. -/
theorem rank_range_lt (hκ : κ.IsInaccessible) {a : ZFSet.{u}} (ha : a.rank < κ.ord)
    (f : Shrink.{u} ↥a → ZFSet.{u}) (hf : ∀ i, (f i).rank < κ.ord) :
    (ZFSet.range f).rank < κ.ord := by
  rw [ZFSet.rank_range]
  refine Cardinal.iSup_lt_ord_of_isRegular hκ.isRegular (mk_shrink_lt hκ a ha) fun i => ?_
  exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt (hf i)

/-! ### `V κ` satisfies the axioms of ZFC (set-theoretic content) -/

/-- The finite von Neumann ordinals, used as a witness for the axiom of infinity. -/
def natSet : ℕ → ZFSet.{u}
  | 0 => ∅
  | (n + 1) => insert (natSet n) (natSet n)

theorem rank_natSet_lt (hκ : κ.IsInaccessible) (n : ℕ) : (natSet.{u} n).rank < κ.ord := by
  induction n with
  | zero =>
    rw [natSet, ZFSet.rank_empty]
    exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).bot_lt
  | succ n ih =>
    rw [natSet, ZFSet.rank_insert]
    exact max_lt ((Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt ih) ih

theorem Vs.ext' {κ : Cardinal.{u}} (x y : Vs κ) (h : ∀ z : Vs κ, z.1 ∈ x.1 ↔ z.1 ∈ y.1) : x = y := by
  refine Subtype.ext (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · exact (h ⟨z, lt_trans (ZFSet.rank_lt_of_mem hz) x.2⟩).1 hz
  · exact (h ⟨z, lt_trans (ZFSet.rank_lt_of_mem hz) y.2⟩).2 hz

theorem Vs.pair (hκ : κ.IsInaccessible) (x y : Vs κ) :
    ∃ p : Vs κ, ∀ z : Vs κ, z.1 ∈ p.1 ↔ (z = x ∨ z = y) := by
  refine ⟨⟨{x.1, y.1}, ?_⟩, fun z => ?_⟩
  · rw [ZFSet.rank_pair]
    exact max_lt ((Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt x.2)
      ((Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt y.2)
  · simp [Subtype.ext_iff]

theorem Vs.union {κ : Cardinal.{u}} (x : Vs κ) :
    ∃ u : Vs κ, ∀ z : Vs κ, z.1 ∈ u.1 ↔ ∃ y : Vs κ, y.1 ∈ x.1 ∧ z.1 ∈ y.1 := by
  refine ⟨⟨⋃₀ x.1, lt_of_le_of_lt (ZFSet.rank_sUnion_le _) x.2⟩, fun z => ?_⟩
  show z.1 ∈ ⋃₀ x.1 ↔ _
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    exact ⟨⟨y, lt_trans (ZFSet.rank_lt_of_mem hy) x.2⟩, hy, hz⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨y.1, hy, hz⟩

theorem Vs.power (hκ : κ.IsInaccessible) (x : Vs κ) :
    ∃ p : Vs κ, ∀ z : Vs κ, z.1 ∈ p.1 ↔ ∀ w : Vs κ, w.1 ∈ z.1 → w.1 ∈ x.1 := by
  refine ⟨⟨ZFSet.powerset x.1, ?_⟩, fun z => ?_⟩
  · rw [ZFSet.rank_powerset]
    exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt x.2
  · show z.1 ∈ ZFSet.powerset x.1 ↔ _
    rw [ZFSet.mem_powerset]
    exact ⟨fun hsub w hw => hsub hw,
      fun h w hw => h ⟨w, lt_trans (ZFSet.rank_lt_of_mem hw) z.2⟩ hw⟩

theorem Vs.sep {κ : Cardinal.{u}} (a : Vs κ) (P : Vs κ → Prop) :
    ∃ b : Vs κ, ∀ x : Vs κ, x.1 ∈ b.1 ↔ (x.1 ∈ a.1 ∧ P x) := by
  classical
  refine ⟨⟨ZFSet.sep (fun y => ∃ h : y.rank < κ.ord, P ⟨y, h⟩) a.1, ?_⟩, fun x => ?_⟩
  · exact lt_of_le_of_lt (ZFSet.rank_mono fun z hz => (ZFSet.mem_sep.mp hz).1) a.2
  · show x.1 ∈ ZFSet.sep (fun y => ∃ h : y.rank < κ.ord, P ⟨y, h⟩) a.1 ↔ _
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, h, hP⟩
      exact ⟨hx, (Subtype.ext rfl : (⟨x.1, h⟩ : Vs κ) = x ) ▸ hP⟩
    · rintro ⟨hx, hP⟩
      exact ⟨hx, x.2, (Subtype.ext rfl : (⟨x.1, x.2⟩ : Vs κ) = x).symm ▸ hP⟩

theorem Vs.coll (hκ : κ.IsInaccessible) (a : Vs κ) (R : Vs κ → Vs κ → Prop)
    (h : ∀ x : Vs κ, x.1 ∈ a.1 → ∃ y : Vs κ, R x y) :
    ∃ b : Vs κ, ∀ x : Vs κ, x.1 ∈ a.1 → ∃ y : Vs κ, y.1 ∈ b.1 ∧ R x y := by
  classical
  have h' : ∀ z : ↥(a.1), ∃ y : Vs κ,
      R ⟨z.1, lt_trans (ZFSet.rank_lt_of_mem z.2) a.2⟩ y := fun z => h _ z.2
  choose g hg using h'
  refine ⟨⟨ZFSet.range (fun i : Shrink.{u} ↥(a.1) => (g ((equivShrink _).symm i)).1),
    rank_range_lt hκ a.2 _ fun i => (g _).2⟩, fun x hx => ?_⟩
  refine ⟨g ⟨x.1, hx⟩, ?_, ?_⟩
  · show _ ∈ ZFSet.range _
    rw [ZFSet.mem_range]
    exact ⟨equivShrink _ ⟨x.1, hx⟩, by rw [Equiv.symm_apply_apply]⟩
  · have := hg ⟨x.1, hx⟩
    rwa [(Subtype.ext rfl : (⟨x.1, lt_trans (ZFSet.rank_lt_of_mem hx) a.2⟩ : Vs κ) = x)] at this

theorem Vs.ac (hκ : κ.IsInaccessible) (a : Vs κ)
    (hne : ∀ x : Vs κ, x.1 ∈ a.1 → ∃ z : Vs κ, z.1 ∈ x.1)
    (hdisj : ∀ x y : Vs κ, x.1 ∈ a.1 → y.1 ∈ a.1 → x ≠ y → ¬∃ z : Vs κ, z.1 ∈ x.1 ∧ z.1 ∈ y.1) :
    ∃ c : Vs κ, ∀ x : Vs κ, x.1 ∈ a.1 → ∃ z : Vs κ, (z.1 ∈ x.1 ∧ z.1 ∈ c.1) ∧
      ∀ w : Vs κ, (w.1 ∈ x.1 ∧ w.1 ∈ c.1) → w = z := by
  classical
  have h' : ∀ z : ↥(a.1), ∃ y : Vs κ, y.1 ∈ z.1 := fun z =>
    hne ⟨z.1, lt_trans (ZFSet.rank_lt_of_mem z.2) a.2⟩ z.2
  choose g hg using h'
  refine ⟨⟨ZFSet.range (fun i : Shrink.{u} ↥(a.1) => (g ((equivShrink _).symm i)).1),
    rank_range_lt hκ a.2 _ fun i => (g _).2⟩, fun x hx => ?_⟩
  refine ⟨g ⟨x.1, hx⟩, ⟨hg ⟨x.1, hx⟩, ?_⟩, ?_⟩
  · show _ ∈ ZFSet.range _
    rw [ZFSet.mem_range]
    exact ⟨equivShrink _ ⟨x.1, hx⟩, by rw [Equiv.symm_apply_apply]⟩
  · rintro w ⟨hwx, hwc⟩
    rw [show ((⟨ZFSet.range (fun i : Shrink.{u} ↥(a.1) => (g ((equivShrink _).symm i)).1),
        rank_range_lt hκ a.2 _ fun i => (g _).2⟩ : Vs κ)).1
      = ZFSet.range (fun i : Shrink.{u} ↥(a.1) => (g ((equivShrink _).symm i)).1) from rfl,
      ZFSet.mem_range] at hwc
    obtain ⟨i, hi⟩ := hwc
    set z' : ↥(a.1) := (equivShrink _).symm i with hz'
    have hwz' : w.1 ∈ z'.1 := by
      rw [← hi] at hwx ⊢
      exact hg z'
    have hxz' : x.1 = z'.1 := by
      by_contra hne'
      refine hdisj x ⟨z'.1, lt_trans (ZFSet.rank_lt_of_mem z'.2) a.2⟩ hx z'.2 ?_ ⟨w, hwx, hwz'⟩
      simpa [Subtype.ext_iff] using hne'
    have : z' = ⟨x.1, hx⟩ := Subtype.ext hxz'.symm
    rw [this] at hi
    exact Subtype.ext hi.symm

theorem Vs.inf (hκ : κ.IsInaccessible) :
    ∃ i : Vs κ, (∃ e : Vs κ, e.1 ∈ i.1 ∧ ∀ w : Vs κ, w.1 ∉ e.1) ∧
      ∀ x : Vs κ, x.1 ∈ i.1 → ∃ y : Vs κ, y.1 ∈ i.1 ∧
        ∀ z : Vs κ, z.1 ∈ y.1 ↔ (z.1 ∈ x.1 ∨ z = x) := by
  have hrank : (ZFSet.range (fun m : ULift.{u} ℕ => natSet.{u} m.down)).rank < κ.ord := by
    rw [ZFSet.rank_range]
    refine Cardinal.iSup_lt_ord_of_isRegular hκ.isRegular ?_ fun m => ?_
    · rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
      exact hκ.aleph0_lt
    · exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt (rank_natSet_lt hκ _)
  refine ⟨⟨ZFSet.range (fun m : ULift.{u} ℕ => natSet.{u} m.down), hrank⟩,
    ⟨⟨∅, by
      rw [ZFSet.rank_empty]
      exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).bot_lt⟩, ?_, ?_⟩, ?_⟩
  · show (∅ : ZFSet.{u}) ∈ ZFSet.range _
    rw [ZFSet.mem_range]
    exact ⟨ULift.up 0, rfl⟩
  · intro w
    exact ZFSet.notMem_empty _
  · intro x hx
    rw [show ((⟨ZFSet.range (fun m : ULift.{u} ℕ => natSet.{u} m.down), hrank⟩ : Vs κ)).1
        = ZFSet.range (fun m : ULift.{u} ℕ => natSet.{u} m.down) from rfl, ZFSet.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨⟨natSet.{u} (m.down + 1), rank_natSet_lt hκ _⟩, ?_, fun z => ?_⟩
    · show natSet.{u} (m.down + 1) ∈ ZFSet.range _
      rw [ZFSet.mem_range]
      exact ⟨ULift.up (m.down + 1), rfl⟩
    · show z.1 ∈ natSet.{u} (m.down + 1) ↔ _
      rw [natSet, ZFSet.mem_insert_iff, hm]
      constructor
      · rintro (h | h)
        · exact Or.inr (Subtype.ext h)
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (congrArg Subtype.val h)

theorem Vs.found {κ : Cardinal.{u}} (a : Vs κ) (h : ∃ x : Vs κ, x.1 ∈ a.1) :
    ∃ x : Vs κ, x.1 ∈ a.1 ∧ ¬∃ y : Vs κ, y.1 ∈ x.1 ∧ y.1 ∈ a.1 := by
  obtain ⟨x0, hx0⟩ := h
  have hne : a.1 ≠ ∅ := fun hz => by
    rw [hz] at hx0
    exact ZFSet.notMem_empty _ hx0
  obtain ⟨y, hya, hinter⟩ := ZFSet.regularity a.1 hne
  refine ⟨⟨y, lt_trans (ZFSet.rank_lt_of_mem hya) a.2⟩, hya, ?_⟩
  rintro ⟨w, hwy, hwa⟩
  have : w.1 ∈ a.1 ∩ y := ZFSet.mem_inter.mpr ⟨hwa, hwy⟩
  rw [hinter] at this
  exact ZFSet.notMem_empty _ this

end Closure

/-! ### Evaluating the satisfaction relation in `V κ` -/

@[simp] theorem relMap_mem {κ : Cardinal.{u}} (x : Fin 2 → Vs κ) :
    Structure.RelMap (M := Vs κ) memSymb x ↔ (x 0).1 ∈ (x 1).1 := Iff.rfl

section Snoc

variable {M : Type*}

@[simp] theorem snoc10 (f : Fin 0 → M) (a : M) : (Fin.snoc f a : Fin 1 → M) 0 = a := rfl
@[simp] theorem snoc20 (f : Fin 1 → M) (a : M) : (Fin.snoc f a : Fin 2 → M) 0 = f 0 := rfl
@[simp] theorem snoc21 (f : Fin 1 → M) (a : M) : (Fin.snoc f a : Fin 2 → M) 1 = a := rfl
@[simp] theorem snoc30 (f : Fin 2 → M) (a : M) : (Fin.snoc f a : Fin 3 → M) 0 = f 0 := rfl
@[simp] theorem snoc31 (f : Fin 2 → M) (a : M) : (Fin.snoc f a : Fin 3 → M) 1 = f 1 := rfl
@[simp] theorem snoc32 (f : Fin 2 → M) (a : M) : (Fin.snoc f a : Fin 3 → M) 2 = a := rfl
@[simp] theorem snoc40 (f : Fin 3 → M) (a : M) : (Fin.snoc f a : Fin 4 → M) 0 = f 0 := rfl
@[simp] theorem snoc41 (f : Fin 3 → M) (a : M) : (Fin.snoc f a : Fin 4 → M) 1 = f 1 := rfl
@[simp] theorem snoc42 (f : Fin 3 → M) (a : M) : (Fin.snoc f a : Fin 4 → M) 2 = f 2 := rfl
@[simp] theorem snoc43 (f : Fin 3 → M) (a : M) : (Fin.snoc f a : Fin 4 → M) 3 = a := rfl
@[simp] theorem snoc50 (f : Fin 4 → M) (a : M) : (Fin.snoc f a : Fin 5 → M) 0 = f 0 := rfl
@[simp] theorem snoc51 (f : Fin 4 → M) (a : M) : (Fin.snoc f a : Fin 5 → M) 1 = f 1 := rfl
@[simp] theorem snoc52 (f : Fin 4 → M) (a : M) : (Fin.snoc f a : Fin 5 → M) 2 = f 2 := rfl
@[simp] theorem snoc53 (f : Fin 4 → M) (a : M) : (Fin.snoc f a : Fin 5 → M) 3 = f 3 := rfl
@[simp] theorem snoc54 (f : Fin 4 → M) (a : M) : (Fin.snoc f a : Fin 5 → M) 4 = a := rfl

variable {n : ℕ}

/-- Reindexing lemma for the separation schema. -/
theorem val_lemma1 (xs : Fin n → M) (a b x : M) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x : Fin (n + 3) → M) ∘
      (fun i : Fin (n + 1) => if (i : ℕ) < n then Fin.castAdd 2 i else Fin.addNat i 2)
      = Fin.snoc xs x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · have h : (Fin.castAdd 2 (Fin.castSucc j) : Fin (n + 3))
        = ((j.castSucc).castSucc).castSucc := Fin.ext (by simp)
    simp [h]

/-- Reindexing lemma for the hypothesis of the collection schema. -/
theorem val_lemma2 (xs : Fin n → M) (a x y : M) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs a) x) y : Fin (n + 3) → M) ∘
      (fun i : Fin (n + 2) => if (i : ℕ) < n then Fin.castAdd 1 i else Fin.addNat i 1)
      = Fin.snoc (Fin.snoc xs x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
  · simp
  · have h : ((Fin.last n).castSucc.succ : Fin (n + 3)) = (Fin.last (n + 1)).castSucc :=
      Fin.ext (by simp)
    simp [h]
  · have h : (Fin.castAdd 1 (Fin.castSucc (Fin.castSucc k)) : Fin (n + 3))
        = ((k.castSucc).castSucc).castSucc := Fin.ext (by simp)
    simp [h]

/-- Reindexing lemma for the conclusion of the collection schema. -/
theorem val_lemma3 (xs : Fin n → M) (a b x y : M) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x) y : Fin (n + 4) → M) ∘
      (fun i : Fin (n + 2) => if (i : ℕ) < n then Fin.castAdd 2 i else Fin.addNat i 2)
      = Fin.snoc (Fin.snoc xs x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
  · simp
  · have h : (((Fin.last n).castSucc).addNat 2 : Fin (n + 4)) = (Fin.last (n + 2)).castSucc :=
      Fin.ext (by simp)
    simp [h]
  · have h : (Fin.castAdd 2 (Fin.castSucc (Fin.castSucc k)) : Fin (n + 4))
        = (((k.castSucc).castSucc).castSucc).castSucc := Fin.ext (by simp)
    simp [h]

end Snoc

/-! ### What the axioms say in an arbitrary structure

These lemmas make the content of each axiom explicit, independently of any particular model. -/

section Faithful

variable {M : Type*} [setLang.Structure M] {n : ℕ}

/-- The interpretation of the membership symbol in an arbitrary structure. -/
abbrev MemR (x y : M) : Prop := Structure.RelMap (M := M) memSymb ![x, y]

theorem realize_extAx_iff : M ⊨ extAx ↔ ∀ x y : M, (∀ z : M, MemR z x ↔ MemR z y) → x = y := by
  simp only [extAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_iff, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_bdEqual, Function.comp_apply, Term.realize_var, Sum.elim_inr,
    snoc10, snoc20, snoc21, snoc30, snoc31, snoc32]

theorem realize_foundAx_iff :
    M ⊨ foundAx ↔ ∀ a : M, (∃ x : M, MemR x a) →
      ∃ x : M, MemR x a ∧ ¬∃ y : M, MemR y x ∧ MemR y a := by
  simp only [foundAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_rel₂, Function.comp_apply,
    Term.realize_var, Sum.elim_inr, snoc10, snoc20, snoc21, snoc30, snoc31, snoc32]

theorem realize_pairAx_iff :
    M ⊨ pairAx ↔ ∀ x y : M, ∃ p : M, ∀ z : M, MemR z p ↔ (z = x ∨ z = y) := by
  simp only [pairAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_sup,
    BoundedFormula.realize_rel₂, BoundedFormula.realize_bdEqual, Function.comp_apply,
    Term.realize_var, Sum.elim_inr, snoc10, snoc20, snoc21, snoc30, snoc31, snoc32,
    snoc40, snoc41, snoc42, snoc43]

theorem realize_unionAx_iff :
    M ⊨ unionAx ↔ ∀ a : M, ∃ u : M, ∀ z : M, MemR z u ↔ ∃ y : M, MemR y a ∧ MemR z y := by
  simp only [unionAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_inf,
    BoundedFormula.realize_rel₂, Function.comp_apply, Term.realize_var, Sum.elim_inr,
    snoc10, snoc20, snoc21, snoc30, snoc31, snoc32, snoc40, snoc42, snoc43]

theorem realize_powerAx_iff :
    M ⊨ powerAx ↔ ∀ a : M, ∃ p : M, ∀ z : M, MemR z p ↔ ∀ w : M, MemR w z → MemR w a := by
  simp only [powerAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_imp,
    BoundedFormula.realize_rel₂, Function.comp_apply, Term.realize_var, Sum.elim_inr,
    snoc10, snoc20, snoc21, snoc30, snoc31, snoc32, snoc40, snoc42, snoc43]

theorem realize_infAx_iff :
    M ⊨ infAx ↔ ∃ i : M, (∃ e : M, MemR e i ∧ ∀ w : M, ¬MemR w e) ∧
      ∀ x : M, MemR x i → ∃ y : M, MemR y i ∧ ∀ z : M, MemR z y ↔ (MemR z x ∨ z = x) := by
  simp only [infAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, BoundedFormula.realize_sup, BoundedFormula.realize_not,
    BoundedFormula.realize_rel₂, BoundedFormula.realize_bdEqual, Function.comp_apply,
    Term.realize_var, Sum.elim_inr, snoc10, snoc20, snoc21, snoc30, snoc31, snoc32,
    snoc41, snoc42, snoc43]

theorem realize_acAx_iff :
    M ⊨ acAx ↔ ∀ a : M, ((∀ x : M, MemR x a → ∃ z : M, MemR z x) ∧
        (∀ x y : M, ((MemR x a ∧ MemR y a) ∧ ¬x = y) → ¬∃ z : M, MemR z x ∧ MemR z y)) →
      ∃ c : M, ∀ x : M, MemR x a → ∃ z : M, (MemR z x ∧ MemR z c) ∧
        ∀ w : M, (MemR w x ∧ MemR w c) → w = z := by
  simp only [acAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_rel₂, BoundedFormula.realize_bdEqual,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, snoc10, snoc20, snoc21, snoc30,
    snoc31, snoc32, snoc41, snoc42, snoc43, snoc51, snoc52, snoc53, snoc54]

theorem realize_sepAx_iff (φ : setLang.BoundedFormula Empty (n + 1)) :
    M ⊨ sepAx φ ↔ ∀ (xs : Fin n → M) (a : M), ∃ b : M, ∀ x : M,
      MemR x b ↔ (MemR x a ∧ φ.Realize default (Fin.snoc xs x)) := by
  simp only [sepAx, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_inf,
    BoundedFormula.realize_rel₂, Function.comp_apply, Term.realize_var, Sum.elim_inr,
    Fin.snoc_last, Fin.snoc_castSucc,
    BoundedFormula.realize_liftAt (show n + 2 ≤ (n + 1) + 1 by omega), val_lemma1]

theorem realize_collAx_iff (φ : setLang.BoundedFormula Empty (n + 2)) :
    M ⊨ collAx φ ↔ ∀ (xs : Fin n → M) (a : M),
      (∀ x : M, MemR x a → ∃ y : M, φ.Realize default (Fin.snoc (Fin.snoc xs x) y)) →
      ∃ b : M, ∀ x : M, MemR x a → ∃ y : M, MemR y b ∧
        φ.Realize default (Fin.snoc (Fin.snoc xs x) y) := by
  simp only [collAx, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_rel₂, Function.comp_apply, Term.realize_var, Sum.elim_inr,
    Fin.snoc_last, Fin.snoc_castSucc,
    BoundedFormula.realize_liftAt (show n + 1 ≤ (n + 2) + 1 by omega), val_lemma2,
    BoundedFormula.realize_liftAt (show n + 2 ≤ (n + 2) + 1 by omega), val_lemma3]

/-- Any model of `ZFCTheory` has at least two elements; in particular the theory is not
satisfied by a one-point structure. -/
theorem exists_ne_of_models [M ⊨ ZFCTheory] : ∃ x y : M, x ≠ y := by
  have hinf : M ⊨ infAx :=
    Theory.realize_sentence_of_mem ZFCTheory (by
      simp only [ZFCTheory, Set.union_assoc, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto)
  obtain ⟨i, ⟨e, hei, he⟩, _⟩ := realize_infAx_iff.mp hinf
  refine ⟨e, i, fun h => ?_⟩
  exact he e (h ▸ hei)

end Faithful

/-! ### `V κ` models each axiom -/

section Models

variable {κ : Cardinal.{u}}

theorem models_extAx : (Vs κ) ⊨ extAx :=
  realize_extAx_iff.mpr fun x y h => Vs.ext' x y h

theorem models_foundAx : (Vs κ) ⊨ foundAx :=
  realize_foundAx_iff.mpr fun a h => Vs.found a h

theorem models_pairAx (hκ : κ.IsInaccessible) : (Vs κ) ⊨ pairAx :=
  realize_pairAx_iff.mpr fun x y => Vs.pair hκ x y

theorem models_unionAx : (Vs κ) ⊨ unionAx :=
  realize_unionAx_iff.mpr fun x => Vs.union x

theorem models_powerAx (hκ : κ.IsInaccessible) : (Vs κ) ⊨ powerAx :=
  realize_powerAx_iff.mpr fun x => Vs.power hκ x

theorem models_infAx (hκ : κ.IsInaccessible) : (Vs κ) ⊨ infAx :=
  realize_infAx_iff.mpr (Vs.inf hκ)

theorem models_acAx (hκ : κ.IsInaccessible) : (Vs κ) ⊨ acAx :=
  realize_acAx_iff.mpr fun a h =>
    Vs.ac hκ a h.1 fun x y hx hy hxy => h.2 x y ⟨⟨hx, hy⟩, hxy⟩

theorem models_sepAx {n : ℕ} (φ : setLang.BoundedFormula Empty (n + 1)) : (Vs κ) ⊨ sepAx φ :=
  realize_sepAx_iff φ |>.mpr fun xs a =>
    Vs.sep a fun x => φ.Realize default (Fin.snoc xs x)

theorem models_collAx (hκ : κ.IsInaccessible) {n : ℕ}
    (φ : setLang.BoundedFormula Empty (n + 2)) : (Vs κ) ⊨ collAx φ :=
  realize_collAx_iff φ |>.mpr fun xs a h =>
    Vs.coll hκ a (fun x y => φ.Realize default (Fin.snoc (Fin.snoc xs x) y)) h

end Models

theorem models_ZFCTheory {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) : (Vs κ) ⊨ ZFCTheory := by
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with (hφ | hφ) | hφ
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extAx
    · exact models_foundAx
    · exact models_pairAx hκ
    · exact models_unionAx
    · exact models_powerAx hκ
    · exact models_infAx hκ
    · exact models_acAx hκ
  · obtain ⟨p, rfl⟩ := hφ
    exact models_sepAx p.2
  · obtain ⟨p, rfl⟩ := hφ
    exact models_collAx hκ p.2

instance instNonemptyVs {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) : Nonempty (Vs κ) :=
  ⟨⟨∅, by
    rw [ZFSet.rank_empty]
    exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).bot_lt⟩⟩

/-- **An inaccessible cardinal yields a model of ZFC**: if there is a (strongly) inaccessible
cardinal, then the first-order theory `ZFCTheory` is satisfiable, i.e. `Con(ZFC)` holds
(semantically). -/
theorem inaccessible_implies_ConZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ZFCTheory.IsSatisfiable := by
  haveI := instNonemptyVs hκ
  haveI := models_ZFCTheory hκ
  exact Theory.Model.isSatisfiable (Vs κ)

/-- `Con(ZFC + "there is an inaccessible") → Con(ZFC)`: any satisfiable theory extending `ZFC`
witnesses the satisfiability of `ZFC`. Instantiating `T` with `ZFC` together with a sentence
asserting the existence of an inaccessible cardinal gives the statement in the title. -/
theorem ConZFC_of_ConZFC_extension {T : setLang.Theory} (hT : ZFCTheory ⊆ T)
    (h : T.IsSatisfiable) : ZFCTheory.IsSatisfiable :=
  h.mono hT

end Frontier

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

