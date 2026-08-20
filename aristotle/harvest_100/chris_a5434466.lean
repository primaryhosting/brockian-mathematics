import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/
def setLang : Language := ⟨fun _ => Empty, memRelSym⟩

/-- The membership relation symbol. -/
abbrev memSym : setLang.Relations 2 := .mem

/-- The atomic formula `t₁ ∈ t₂`. -/
abbrev memF {α : Type*} {n : ℕ} (t₁ t₂ : setLang.Term (α ⊕ Fin n)) : setLang.BoundedFormula α n :=
  memSym.boundedFormula₂ t₁ t₂

/-! ## The axioms of ZFC -/

/-- Extensionality: `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
def axExt : setLang.Sentence :=
  ∀' ∀' ((∀' (memF (&2) (&0) ⇔ memF (&2) (&1))) ⟹ (&0 =' &1))

/-- Empty set: `∃ x, ∀ y, y ∉ x`. -/
def axEmpty : setLang.Sentence :=
  ∃' ∀' ∼(memF (&1) (&0))

/-- Pairing: `∀ a b, ∃ y, ∀ z, z ∈ y ↔ (z = a ∨ z = b)`. -/
def axPair : setLang.Sentence :=
  ∀' ∀' ∃' ∀' (memF (&3) (&2) ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))

/-- Union: `∀ x, ∃ y, ∀ w, w ∈ y ↔ ∃ z, z ∈ x ∧ w ∈ z`. -/
def axUnion : setLang.Sentence :=
  ∀' ∃' ∀' (memF (&2) (&1) ⇔ ∃' ((memF (&3) (&0)) ⊓ (memF (&2) (&3))))

/-- Power set: `∀ x, ∃ y, ∀ z, z ∈ y ↔ ∀ w, w ∈ z → w ∈ x`. -/
def axPow : setLang.Sentence :=
  ∀' ∃' ∀' (memF (&2) (&1) ⇔ ∀' ((memF (&3) (&2)) ⟹ (memF (&3) (&0))))

/-- Infinity: there is a set containing an empty set and closed under `y ↦ y ∪ {y}`. -/
def axInf : setLang.Sentence :=
  ∃' ((∃' ((memF (&1) (&0)) ⊓ (∀' ∼(memF (&2) (&1))))) ⊓
      (∀' ((memF (&1) (&0)) ⟹
        ∃' ((memF (&2) (&0)) ⊓
          ∀' ((memF (&3) (&2)) ⇔ ((memF (&3) (&1)) ⊔ (&3 =' &1)))))))

/-- Foundation: every nonempty set has an `∈`-minimal element. -/
def axFound : setLang.Sentence :=
  ∀' ((∃' (memF (&1) (&0))) ⟹
    ∃' ((memF (&1) (&0)) ⊓ ∀' ∼((memF (&2) (&1)) ⊓ (memF (&2) (&0)))))

/-- Choice, in the form: for every set `x` of nonempty, pairwise disjoint sets there is a set
meeting each element of `x` in exactly one point. -/
def axChoice : setLang.Sentence :=
  ∀' (((∀' ((memF (&1) (&0)) ⟹ ∃' (memF (&2) (&1)))) ⊓
       (∀' ((memF (&1) (&0)) ⟹ ∀' ((memF (&2) (&0)) ⟹
         ((&1 =' &2) ⊔ ∀' ∼((memF (&3) (&1)) ⊓ (memF (&3) (&2)))))))) ⟹
    ∃' (∀' ((memF (&2) (&0)) ⟹
      ∃' (((memF (&3) (&2)) ⊓ (memF (&3) (&1))) ⊓
        ∀' (((memF (&4) (&2)) ⊓ (memF (&4) (&1))) ⟹ (&4 =' &3))))))

/-- The separation schema. For a formula `φ` whose free variables are `n` parameters together
with two bound variables, standing for the ambient set `x` and the element `z`, this is the
sentence `∀ params, ∀ x, ∃ y, ∀ z, (z ∈ y ↔ z ∈ x ∧ φ)`. -/
noncomputable def axSep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 2) : setLang.Sentence :=
  Formula.iAlls (Fin n) (∀' ∃' ∀' ((memF (&2) (&1)) ⇔ ((memF (&2) (&0)) ⊓ φ.liftAt 1 1)))

/-- The replacement schema. For a formula `φ` whose free variables are `n` parameters together
with three bound variables, standing for the ambient set `x`, the element `z` and the value `w`,
this is the sentence
`∀ params, ∀ x, (∀ z ∈ x, ∃! w, φ) → ∃ y, ∀ z ∈ x, ∀ w, φ → w ∈ y`,
i.e. the image of `x` under the class function defined by `φ` is contained in a set. Together
with separation this gives the usual form of replacement. -/
noncomputable def axRep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 3) : setLang.Sentence :=
  Formula.iAlls (Fin n)
    (∀' ((∀' ((memF (&1) (&0)) ⟹ ∃' (φ ⊓ ∀' ((φ.liftAt 1 2) ⟹ (&3 =' &2))))) ⟹
      ∃' (∀' ((memF (&2) (&0)) ⟹ ∀' ((φ.liftAt 1 1) ⟹ (memF (&3) (&1)))))))

/-- The theory ZFC in the language of set theory. -/
def ZFCTheory : setLang.Theory :=
  {axExt, axEmpty, axPair, axUnion, axPow, axInf, axFound, axChoice} ∪
    {σ | ∃ (n : ℕ) (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 2), σ = axSep φ} ∪
    {σ | ∃ (n : ℕ) (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 3), σ = axRep φ}

/-! ## Realization of the axioms in an arbitrary structure -/

section MatrixLemmas

@[simp] lemma snoc0_eq {M : Type*} (a : M) :
    (Fin.snoc (default : Fin 0 → M) a) = ![a] := by
  funext i; fin_cases i; rfl

@[simp] lemma snoc1_eq {M : Type*} (a b : M) : (Fin.snoc ![a] b) = ![a, b] := by
  funext i; fin_cases i <;> rfl

@[simp] lemma snoc2_eq {M : Type*} (a b c : M) : (Fin.snoc ![a, b] c) = ![a, b, c] := by
  funext i; fin_cases i <;> rfl

@[simp] lemma snoc3_eq {M : Type*} (a b c d : M) : (Fin.snoc ![a, b, c] d) = ![a, b, c, d] := by
  funext i; fin_cases i <;> rfl

@[simp] lemma snoc4_eq {M : Type*} (a b c d e : M) :
    (Fin.snoc ![a, b, c, d] e) = ![a, b, c, d, e] := by
  funext i; fin_cases i <;> rfl

@[simp] lemma comp_lift2_1 {M : Type*} (a b c : M) :
    ![a, b, c] ∘ (fun i : Fin 2 => if i = 0 then i.castSucc else i.succ) = ![a, c] := by
  funext i; fin_cases i <;> simp

@[simp] lemma comp_lift3_2 {M : Type*} (a b c d : M) :
    ![a, b, c, d] ∘ (fun i : Fin 3 => if (i : ℕ) < 2 then i.castSucc else i.succ) = ![a, b, d] := by
  funext i; fin_cases i <;> simp

@[simp] lemma comp_lift3_1 {M : Type*} (a b c d : M) :
    ![a, b, c, d] ∘ (fun i : Fin 3 => if i = 0 then i.castSucc else i.succ) = ![a, c, d] := by
  funext i; fin_cases i <;> simp

end MatrixLemmas

section Realize

variable {M : Type*} [setLang.Structure M]

/-- The membership relation of a structure in the language of set theory. -/
abbrev memR (a b : M) : Prop := Structure.RelMap memSym ![a, b]

theorem realize_axExt : (M ⊨ axExt) ↔ ∀ a b : M, (∀ z, memR z a ↔ memR z b) → a = b := by
  simp [axExt, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_rel₂, BoundedFormula.realize_bdEqual,
    memR]

theorem realize_axEmpty : (M ⊨ axEmpty) ↔ ∃ x : M, ∀ y : M, ¬ memR y x := by
  simp [axEmpty, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂, memR]

theorem realize_axPair :
    (M ⊨ axPair) ↔ ∀ a b : M, ∃ y : M, ∀ z : M, memR z y ↔ (z = a ∨ z = b) := by
  simp [axPair, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_bdEqual, BoundedFormula.realize_sup, memR]

theorem realize_axUnion :
    (M ⊨ axUnion) ↔ ∀ x : M, ∃ y : M, ∀ w : M, memR w y ↔ ∃ z : M, memR z x ∧ memR w z := by
  simp [axUnion, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_inf, memR]

theorem realize_axPow :
    (M ⊨ axPow) ↔ ∀ x : M, ∃ y : M, ∀ z : M, memR z y ↔ ∀ w : M, memR w z → memR w x := by
  simp [axPow, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_imp, memR]

theorem realize_axInf :
    (M ⊨ axInf) ↔ ∃ x : M, (∃ e : M, memR e x ∧ ∀ y : M, ¬ memR y e) ∧
      ∀ y : M, memR y x → ∃ s : M, memR s x ∧ ∀ w : M, memR w s ↔ (memR w y ∨ w = y) := by
  simp [axInf, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_inf, BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual,
    memR]

theorem realize_axFound :
    (M ⊨ axFound) ↔ ∀ x : M, (∃ y : M, memR y x) →
      ∃ y : M, memR y x ∧ ∀ z : M, ¬ (memR z y ∧ memR z x) := by
  simp [axFound, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂, BoundedFormula.realize_inf,
    memR]

theorem realize_axChoice :
    (M ⊨ axChoice) ↔ ∀ x : M,
      ((∀ z : M, memR z x → ∃ w : M, memR w z) ∧
        (∀ z : M, memR z x → ∀ z' : M, memR z' x →
          (z = z' ∨ ∀ w : M, ¬ (memR w z ∧ memR w z')))) →
      ∃ c : M, ∀ z : M, memR z x →
        ∃ w : M, (memR w z ∧ memR w c) ∧ ∀ w' : M, (memR w' z ∧ memR w' c) → w' = w := by
  simp [axChoice, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, memR]

theorem realize_axSep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 2) :
    (M ⊨ axSep φ) ↔ ∀ p : Fin n → M, ∀ x : M, ∃ y : M, ∀ z : M,
      memR z y ↔ (memR z x ∧ φ.Realize (Sum.elim default p) ![x, z]) := by
  simp [axSep, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_rel₂, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, BoundedFormula.realize_liftAt_one, memR]

theorem realize_axRep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 3) :
    (M ⊨ axRep φ) ↔ ∀ p : Fin n → M, ∀ x : M,
      (∀ z : M, memR z x → ∃! w : M, φ.Realize (Sum.elim default p) ![x, z, w]) →
      ∃ y : M, ∀ z : M, memR z x → ∀ w : M,
        φ.Realize (Sum.elim default p) ![x, z, w] → memR w y := by
  simp [axRep, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, BoundedFormula.realize_liftAt_one, memR,
    ExistsUnique]

end Realize

/-! ## Closure properties of `V_ o` -/

section VonNeumann

variable {o : Ordinal.{u}} {x y : ZFSet.{u}}

theorem mem_V_of_rank_lt (h : rank x < o) : x ∈ V_ o := mem_vonNeumann.2 h

theorem rank_lt_of_mem_V (h : x ∈ V_ o) : rank x < o := mem_vonNeumann.1 h

theorem empty_mem_V (ho : 0 < o) : (∅ : ZFSet.{u}) ∈ V_ o :=
  mem_V_of_rank_lt (by rw [rank_empty]; exact ho)

theorem insert_mem_V (hlim : IsSuccLimit o) (hx : x ∈ V_ o) (hy : y ∈ V_ o) :
    insert x y ∈ V_ o := by
  refine mem_V_of_rank_lt ?_
  rw [rank_insert]
  exact max_lt (hlim.succ_lt (rank_lt_of_mem_V hx)) (rank_lt_of_mem_V hy)

theorem pair_mem_V (hlim : IsSuccLimit o) (hx : x ∈ V_ o) (hy : y ∈ V_ o) :
    ({x, y} : ZFSet.{u}) ∈ V_ o :=
  insert_mem_V hlim hx (insert_mem_V hlim hy (empty_mem_V hlim.bot_lt))

theorem sUnion_mem_V (hx : x ∈ V_ o) : ⋃₀ x ∈ V_ o :=
  mem_V_of_rank_lt (lt_of_le_of_lt (rank_sUnion_le x) (rank_lt_of_mem_V hx))

theorem powerset_mem_V (hlim : IsSuccLimit o) (hx : x ∈ V_ o) : powerset x ∈ V_ o := by
  refine mem_V_of_rank_lt ?_
  rw [rank_powerset]
  exact hlim.succ_lt (rank_lt_of_mem_V hx)

theorem subset_mem_V (hx : x ∈ V_ o) (hsub : y ⊆ x) : y ∈ V_ o :=
  mem_V_of_rank_lt (lt_of_le_of_lt (rank_mono hsub) (rank_lt_of_mem_V hx))

theorem mem_mem_V (hx : x ∈ V_ o) (hy : y ∈ x) : y ∈ V_ o :=
  isTransitive_vonNeumann o x hx hy

theorem vonNeumann_omega_mem_V (h : ω < o) : V_ (ω : Ordinal.{u}) ∈ V_ o :=
  mem_V_of_rank_lt (by rw [rank_vonNeumann]; exact h)

end VonNeumann

/-! ## Cardinal arithmetic at an inaccessible cardinal -/

section Inaccessible

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal, the beth function stays below it. -/
theorem preBeth_lt_of_lt_ord (hκ : κ.IsInaccessible) {a : Ordinal.{u}} (h : a < κ.ord) :
    preBeth a < κ := by
  induction a using Ordinal.induction with
  | h a IH =>
  rw [preBeth, ← Equiv.iSup_comp (α := Cardinal.{u})
      (g := fun b : Set.Iio a => 2 ^ preBeth (b : Ordinal.{u}))
      (Ordinal.ToType.mk (o := a)).symm.toEquiv]
  refine Cardinal.iSup_lt_of_isRegular hκ.isRegular ?_ ?_
  · rw [Cardinal.mk_toType]
    exact Cardinal.lt_ord.1 h
  · intro i
    have hlt : ((Ordinal.ToType.mk (o := a)).symm i : Ordinal.{u}) < a :=
      ((Ordinal.ToType.mk (o := a)).symm i).2
    exact hκ.isStrongLimit.two_power_lt (IH _ hlt (lt_trans hlt h))

/-- Every element of `V_ κ.ord` has cardinality less than `κ`. -/
theorem card_lt_of_mem_V (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x ∈ V_ κ.ord) :
    ZFSet.card x < κ := by
  have h1 : ZFSet.card x ≤ ZFSet.card (V_ (rank x)) := ZFSet.card_mono (subset_vonNeumann_self x)
  rw [card_vonNeumann] at h1
  exact lt_of_le_of_lt h1 (preBeth_lt_of_lt_ord hκ (rank_lt_of_mem_V hx))

/-- `V_ κ.ord` is closed under images of families indexed by one of its elements: this is the
key use of inaccessibility (regularity plus the strong limit property). -/
theorem range_mem_V (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x ∈ V_ κ.ord)
    (f : ↥x → ZFSet.{u}) (hf : ∀ i, f i ∈ V_ κ.ord) : ZFSet.range f ∈ V_ κ.ord := by
  rw [mem_vonNeumann, rank_range]
  rw [← Equiv.iSup_comp (α := Ordinal.{u}) (g := fun i : ↥x => succ (rank (f i)))
    (equivShrink.{u} ↥x).symm]
  refine Cardinal.iSup_lt_ord_lift_of_isRegular hκ.isRegular ?_ ?_
  · simpa [ZFSet.card] using card_lt_of_mem_V hκ hx
  · intro i
    exact (isSuccLimit_ord hκ.aleph0_lt.le).succ_lt (rank_lt_of_mem_V (hf _))

end Inaccessible

/-! ## The model -/

section Model

variable {o : Ordinal.{u}}

/-- The universe of the model: the elements of `V_ o`. -/
def VSet (o : Ordinal.{u}) : Type (u + 1) := {x : ZFSet.{u} // x ∈ V_ o}

instance : CoeOut (VSet o) ZFSet.{u} := ⟨Subtype.val⟩

instance vSetStructure (o : Ordinal.{u}) : setLang.Structure (VSet o) where
  funMap {_} f := f.elim
  RelMap {n} r := match n, r with
    | 2, memRelSym.mem => fun v => ((v 0 : VSet o) : ZFSet.{u}) ∈ ((v 1 : VSet o) : ZFSet.{u})

@[simp] theorem memR_VSet (a b : VSet o) : memR a b ↔ (a : ZFSet.{u}) ∈ (b : ZFSet.{u}) :=
  Iff.rfl

@[simp] theorem VSet.ext_iff' (a b : VSet o) : a = b ↔ (a : ZFSet.{u}) = (b : ZFSet.{u}) :=
  Subtype.ext_iff

theorem VSet.nonempty (ho : 0 < o) : Nonempty (VSet o) := ⟨⟨∅, empty_mem_V ho⟩⟩

theorem model_axExt : VSet o ⊨ axExt := by
  rw [realize_axExt]
  intro a b h
  refine Subtype.ext (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · exact (h ⟨z, mem_mem_V a.2 hz⟩).1 hz
  · exact (h ⟨z, mem_mem_V b.2 hz⟩).2 hz

theorem model_axEmpty (ho : 0 < o) : VSet o ⊨ axEmpty := by
  rw [realize_axEmpty]
  exact ⟨⟨∅, empty_mem_V ho⟩, fun y => ZFSet.notMem_empty _⟩

theorem model_axPair (hlim : IsSuccLimit o) : VSet o ⊨ axPair := by
  rw [realize_axPair]
  intro a b
  refine ⟨⟨({(a : ZFSet), (b : ZFSet)} : ZFSet), pair_mem_V hlim a.2 b.2⟩, fun z => ?_⟩
  simp

theorem model_axUnion : VSet o ⊨ axUnion := by
  rw [realize_axUnion]
  intro x
  refine ⟨⟨⋃₀ (x : ZFSet), sUnion_mem_V x.2⟩, fun w => ?_⟩
  constructor
  · intro hw
    obtain ⟨z, hz, hwz⟩ := ZFSet.mem_sUnion.1 hw
    exact ⟨⟨z, mem_mem_V x.2 hz⟩, hz, hwz⟩
  · rintro ⟨z, hz, hwz⟩
    exact ZFSet.mem_sUnion.2 ⟨(z : ZFSet), hz, hwz⟩

theorem model_axPow (hlim : IsSuccLimit o) : VSet o ⊨ axPow := by
  rw [realize_axPow]
  intro x
  refine ⟨⟨powerset (x : ZFSet), powerset_mem_V hlim x.2⟩, fun z => ?_⟩
  constructor
  · intro hz w hw
    exact ZFSet.mem_powerset.1 hz hw
  · intro h
    exact ZFSet.mem_powerset.2 fun w hw => h ⟨w, mem_mem_V z.2 hw⟩ hw

theorem model_axInf (hω : ω < o) : VSet o ⊨ axInf := by
  rw [realize_axInf]
  have hVω : V_ (ω : Ordinal.{u}) ∈ V_ o := vonNeumann_omega_mem_V hω
  have hemp : (∅ : ZFSet.{u}) ∈ V_ (ω : Ordinal.{u}) := empty_mem_V omega0_pos
  refine ⟨⟨V_ (ω : Ordinal.{u}), hVω⟩,
    ⟨⟨∅, mem_mem_V hVω hemp⟩, hemp, fun y => ZFSet.notMem_empty _⟩, ?_⟩
  intro y hy
  have hins : insert (y : ZFSet) (y : ZFSet) ∈ V_ (ω : Ordinal.{u}) :=
    insert_mem_V isSuccLimit_omega0 hy hy
  refine ⟨⟨insert (y : ZFSet) (y : ZFSet), mem_mem_V hVω hins⟩, hins, fun w => ?_⟩
  simp [ZFSet.mem_insert_iff, or_comm]

theorem model_axFound : VSet o ⊨ axFound := by
  rw [realize_axFound]
  rintro x ⟨y0, hy0⟩
  simp only [memR_VSet] at hy0
  have hne : (x : ZFSet) ≠ ∅ := by
    intro h
    rw [h] at hy0
    exact ZFSet.notMem_empty _ hy0
  obtain ⟨y, hy, hinter⟩ := ZFSet.regularity (x : ZFSet) hne
  refine ⟨⟨y, mem_mem_V x.2 hy⟩, hy, fun z => ?_⟩
  rintro ⟨hzy, hzx⟩
  have hmem : (z : ZFSet) ∈ (x : ZFSet) ∩ y := ZFSet.mem_inter.2 ⟨hzx, hzy⟩
  rw [hinter] at hmem
  exact ZFSet.notMem_empty _ hmem

theorem model_axSep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 2) :
    VSet o ⊨ axSep φ := by
  rw [realize_axSep]
  intro p x
  refine ⟨⟨ZFSet.sep (fun z => ∃ h : z ∈ V_ o,
      φ.Realize (Sum.elim default p) ![x, ⟨z, h⟩]) (x : ZFSet),
    subset_mem_V x.2 ZFSet.sep_subset⟩, fun z => ?_⟩
  rw [memR_VSet, ZFSet.mem_sep]
  constructor
  · rintro ⟨hzx, _, hφ⟩
    exact ⟨hzx, hφ⟩
  · rintro ⟨hzx, hφ⟩
    exact ⟨hzx, z.2, hφ⟩

variable {κ : Cardinal.{u}}

theorem model_axRep (hκ : κ.IsInaccessible) {n : ℕ}
    (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 3) : VSet κ.ord ⊨ axRep φ := by
  rw [realize_axRep]
  intro p x hfun
  choose f hf huniq using fun z : ↥(x : ZFSet) =>
    hfun ⟨(z : ZFSet), mem_mem_V x.2 z.2⟩ z.2
  refine ⟨⟨ZFSet.range (fun z => ((f z : VSet κ.ord) : ZFSet)),
    range_mem_V hκ x.2 _ (fun z => (f z).2)⟩, ?_⟩
  intro z hz w hw
  have huw := huniq ⟨(z : ZFSet), hz⟩ w hw
  rw [memR_VSet, ZFSet.mem_range]
  exact ⟨⟨(z : ZFSet), hz⟩, by rw [← huw]⟩

theorem model_axChoice (hκ : κ.IsInaccessible) : VSet κ.ord ⊨ axChoice := by
  rw [realize_axChoice]
  rintro x ⟨hne, hdisj⟩
  choose g hg using fun z : ↥((x : VSet κ.ord) : ZFSet) =>
    hne ⟨(z : ZFSet), mem_mem_V x.2 z.2⟩ z.2
  refine ⟨⟨ZFSet.range (fun z => ((g z : VSet κ.ord) : ZFSet)),
    range_mem_V hκ x.2 _ (fun z => (g z).2)⟩, ?_⟩
  intro z hz
  simp only [memR_VSet] at hz
  refine ⟨g ⟨(z : ZFSet), hz⟩, ⟨hg _, ZFSet.mem_range.2 ⟨⟨(z : ZFSet), hz⟩, rfl⟩⟩, ?_⟩
  rintro w' ⟨hw'z, hw'c⟩
  simp only [memR_VSet] at hw'z hw'c
  obtain ⟨z', hz'⟩ := ZFSet.mem_range.1 hw'c
  have hzz' : z = (⟨(z' : ZFSet), mem_mem_V x.2 z'.2⟩ : VSet κ.ord) := by
    rcases hdisj z hz ⟨(z' : ZFSet), mem_mem_V x.2 z'.2⟩ z'.2 with h | h
    · exact h
    · exact (h w' ⟨hw'z, by simpa only [memR_VSet, hz'] using hg z'⟩).elim
  have hval : ((z : VSet κ.ord) : ZFSet) = ((z' : ↥((x : VSet κ.ord) : ZFSet)) : ZFSet) :=
    congrArg Subtype.val hzz'
  have hidx : (⟨(z : ZFSet), hz⟩ : ↥((x : VSet κ.ord) : ZFSet)) = z' := Subtype.ext hval
  rw [hidx]
  exact Subtype.ext hz'.symm

theorem model_ZFCTheory (hκ : κ.IsInaccessible) : VSet κ.ord ⊨ ZFCTheory := by
  have hℵ : (ℵ₀ : Cardinal.{u}) ≤ κ := hκ.aleph0_lt.le
  have hlim : IsSuccLimit κ.ord := isSuccLimit_ord hℵ
  have h0 : (0 : Ordinal.{u}) < κ.ord := hlim.bot_lt
  have hω : (ω : Ordinal.{u}) < κ.ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.2 hκ.aleph0_lt
  rw [Theory.model_iff]
  rintro σ ((hσ | ⟨n, φ, rfl⟩) | ⟨n, φ, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact model_axExt
    · exact model_axEmpty h0
    · exact model_axPair hlim
    · exact model_axUnion
    · exact model_axPow hlim
    · exact model_axInf hω
    · exact model_axFound
    · exact model_axChoice hκ
  · exact model_axSep φ
  · exact model_axRep hκ φ

end Model

/-! ## Main results -/

/-- **An inaccessible cardinal yields a model of ZFC.** If there is an inaccessible cardinal
`κ`, then `V_ κ` is a model of ZFC, hence ZFC is satisfiable (consistent). -/
theorem inaccessible_implies_ConZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ZFCTheory.IsSatisfiable := by
  haveI : Nonempty (VSet κ.ord) := VSet.nonempty (isSuccLimit_ord hκ.aleph0_lt.le).bot_lt
  haveI : VSet κ.ord ⊨ ZFCTheory := model_ZFCTheory hκ
  exact Theory.Model.isSatisfiable (VSet κ.ord)

/-- A sanity check that `ZFCTheory` is not trivially satisfiable: no structure with at most
one element is a model of it. -/
theorem not_model_ZFCTheory_of_subsingleton {M : Type*} [setLang.Structure M] [Nonempty M]
    [Subsingleton M] : ¬ (M ⊨ ZFCTheory) := by
  intro hM
  have hE : M ⊨ axEmpty := hM.realize_of_mem _ (by
    simp only [ZFCTheory, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto)
  have hP : M ⊨ axPair := hM.realize_of_mem _ (by
    simp only [ZFCTheory, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto)
  rw [realize_axEmpty] at hE
  rw [realize_axPair] at hP
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hP x x
  exact hx x (Subsingleton.elim y x ▸ (hy x).2 (Or.inl rfl))

/-- Consequently, `Con(ZFC + φ) → Con(ZFC)` for any sentence `φ`; in particular for the
statement that an inaccessible cardinal exists. -/
theorem ConZFC_of_ConZFC_add {φ : setLang.Sentence} (h : (insert φ ZFCTheory).IsSatisfiable) :
    ZFCTheory.IsSatisfiable :=
  h.mono (Set.subset_insert _ _)

end Frontier

