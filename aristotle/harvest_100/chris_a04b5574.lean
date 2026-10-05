import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The first-order language of set theory

We build the first-order language with a single binary relation symbol `∈`, write down a
standard axiomatization of `ZFC` in it (extensionality, empty set, pairing, union, power set,
infinity, foundation, choice, together with the separation and replacement schemes), and prove
that Mathlib's type `ZFSet` of ZFC-sets is a model of this theory.
-/

namespace Frontier

open FirstOrder Language

universe u

/-- The relation symbols of the language of set theory: a single binary relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory. -/
def setLang : Language := ⟨fun _ => Empty, memRel⟩

/-- The membership relation symbol. -/
abbrev memSymb : setLang.Relations 2 := memRel.mem

/-- `ZFSet` is a structure in the language of set theory. -/
instance zfSetStructure : setLang.Structure ZFSet.{u} where
  funMap {_} f := Empty.elim f
  RelMap {n} r := match n, r with
    | 2, memRel.mem => fun x => x 0 ∈ x 1

@[simp] theorem relMap_mem {x : Fin 2 → ZFSet.{u}} :
    Structure.RelMap (L := setLang) (M := ZFSet.{u}) memRel.mem x ↔ (x 0 ∈ x 1) := Iff.rfl

/-- The atomic formula `xᵢ ∈ xⱼ`. -/
def memF {n : ℕ} (i j : Fin n) : setLang.BoundedFormula Empty n :=
  memSymb.boundedFormula₂ (Term.var (Sum.inr i)) (Term.var (Sum.inr j))

/-- The atomic formula `xᵢ = xⱼ`. -/
def eqF {n : ℕ} (i j : Fin n) : setLang.BoundedFormula Empty n :=
  Term.bdEqual (Term.var (Sum.inr i)) (Term.var (Sum.inr j))

@[simp] theorem realize_memF {n : ℕ} (i j : Fin n) (v : Empty → ZFSet.{u})
    (xs : Fin n → ZFSet.{u}) : (memF i j).Realize v xs ↔ xs i ∈ xs j := by
  simp [memF]

@[simp] theorem realize_eqF {n : ℕ} (i j : Fin n) (v : Empty → ZFSet.{u})
    (xs : Fin n → ZFSet.{u}) : (eqF i j).Realize v xs ↔ xs i = xs j := by
  simp [eqF]

/-- Substituting bound variables for the free variables of a formula. -/
def subst₀ {k m : ℕ} (φ : setLang.Formula (Fin k)) (g : Fin k → Fin m) :
    setLang.BoundedFormula Empty m :=
  BoundedFormula.relabel (fun i => Sum.inr (g i)) φ

@[simp] theorem realize_subst₀ {k m : ℕ} (φ : setLang.Formula (Fin k)) (g : Fin k → Fin m)
    (v : Empty → ZFSet.{u}) (xs : Fin m → ZFSet.{u}) :
    (subst₀ φ g).Realize v xs ↔ φ.Realize (xs ∘ g) := by
  rw [subst₀, BoundedFormula.realize_relabel]
  have h1 : (Sum.elim v (xs ∘ Fin.castAdd 0) ∘ fun i => Sum.inr (g i)) = xs ∘ g := by
    funext i; simp
  rw [h1, Formula.Realize]
  exact iff_of_eq (congrArg (fun t => BoundedFormula.Realize φ (xs ∘ g) t)
    (Subsingleton.elim _ _))

/-- Evaluation of `Fin.snoc` below the top index. -/
theorem snoc_lt {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) (i : Fin (n + 1)) (h : (i : ℕ) < n) :
    (Fin.snoc f x : Fin (n + 1) → α) i = f ⟨i, h⟩ := by
  simp [Fin.snoc, h, Fin.castLT]

/-- Evaluation of `Fin.snoc` at the top index. -/
theorem snoc_eq {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) (i : Fin (n + 1)) (h : (i : ℕ) = n) :
    (Fin.snoc f x : Fin (n + 1) → α) i = x := by
  simp [Fin.snoc, h]

theorem snoc2_k {α : Type*} {k : ℕ} (xs : Fin k → α) (a b : α) (h : k < k + 2) :
    (Fin.snoc (Fin.snoc xs a) b : Fin (k + 2) → α) ⟨k, h⟩ = a := by
  rw [snoc_lt _ _ _ (show k < k + 1 by omega)]
  exact snoc_eq _ _ _ rfl

theorem snoc2_k1 {α : Type*} {k : ℕ} (xs : Fin k → α) (a b : α) (h : k + 1 < k + 2) :
    (Fin.snoc (Fin.snoc xs a) b : Fin (k + 2) → α) ⟨k + 1, h⟩ = b :=
  snoc_eq _ _ _ rfl

theorem snoc3_lt {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c : α) (j : ℕ) (h : j < k + 3)
    (h' : j < k) : (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c : Fin (k + 3) → α) ⟨j, h⟩
      = xs ⟨j, h'⟩ := by
  rw [snoc_lt _ _ _ (show j < k + 2 by omega), snoc_lt _ _ _ (show j < k + 1 by omega),
    snoc_lt _ _ _ h']

theorem snoc3_k {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c : α) (h : k < k + 3) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c : Fin (k + 3) → α) ⟨k, h⟩ = a := by
  rw [snoc_lt _ _ _ (show k < k + 2 by omega), snoc_lt _ _ _ (show k < k + 1 by omega)]
  exact snoc_eq _ _ _ rfl

theorem snoc3_k1 {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c : α) (h : k + 1 < k + 3) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c : Fin (k + 3) → α) ⟨k + 1, h⟩ = b := by
  rw [snoc_lt _ _ _ (show k + 1 < k + 2 by omega)]
  exact snoc_eq _ _ _ rfl

theorem snoc3_k2 {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c : α) (h : k + 2 < k + 3) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c : Fin (k + 3) → α) ⟨k + 2, h⟩ = c :=
  snoc_eq _ _ _ rfl

theorem snoc4_lt {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c d : α) (j : ℕ) (h : j < k + 4)
    (h' : j < k) : (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c) d : Fin (k + 4) → α) ⟨j, h⟩
      = xs ⟨j, h'⟩ := by
  rw [snoc_lt _ _ _ (show j < k + 3 by omega)]
  exact snoc3_lt _ _ _ _ _ _ h'

theorem snoc4_k {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c d : α) (h : k < k + 4) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c) d : Fin (k + 4) → α) ⟨k, h⟩ = a := by
  rw [snoc_lt _ _ _ (show k < k + 3 by omega)]
  exact snoc3_k _ _ _ _ _

theorem snoc4_k1 {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c d : α) (h : k + 1 < k + 4) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c) d : Fin (k + 4) → α) ⟨k + 1, h⟩ = b := by
  rw [snoc_lt _ _ _ (show k + 1 < k + 3 by omega)]
  exact snoc3_k1 _ _ _ _ _

theorem snoc4_k2 {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c d : α) (h : k + 2 < k + 4) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c) d : Fin (k + 4) → α) ⟨k + 2, h⟩ = c := by
  rw [snoc_lt _ _ _ (show k + 2 < k + 3 by omega)]
  exact snoc3_k2 _ _ _ _ _

theorem snoc4_k3 {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c d : α) (h : k + 3 < k + 4) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c) d : Fin (k + 4) → α) ⟨k + 3, h⟩ = d :=
  snoc_eq _ _ _ rfl

/-- The valuation sending variable `0` to `x` and variable `i + 1` to `ps i`. -/
def extVal₁ {k : ℕ} (x : ZFSet.{u}) (ps : Fin k → ZFSet.{u}) : Fin (k + 1) → ZFSet.{u} :=
  fun i => if h : (i : ℕ) = 0 then x else ps ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

/-- The valuation sending variable `0` to `x`, variable `1` to `y` and variable `i + 2` to
`ps i`. -/
def extVal₂ {k : ℕ} (x y : ZFSet.{u}) (ps : Fin k → ZFSet.{u}) : Fin (k + 2) → ZFSet.{u} :=
  fun i => if h : (i : ℕ) = 0 then x else if h' : (i : ℕ) = 1 then y
    else ps ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩

/-! ### The axioms of ZFC -/

/-- Extensionality. -/
def extensionalityAx : setLang.Sentence :=
  ∀' ∀' ((∀' ((memF 2 0) ⇔ (memF 2 1))) ⟹ (eqF 0 1))

/-- Existence of the empty set. -/
def emptySetAx : setLang.Sentence :=
  ∃' ∀' (∼ (memF 1 0))

/-- Pairing. -/
def pairingAx : setLang.Sentence :=
  ∀' ∀' ∃' ∀' ((memF 3 2) ⇔ ((eqF 3 0) ⊔ (eqF 3 1)))

/-- Union. -/
def unionAx : setLang.Sentence :=
  ∀' ∃' ∀' ((memF 2 1) ⇔ ∃' ((memF 3 0) ⊓ (memF 2 3)))

/-- Power set. -/
def powerSetAx : setLang.Sentence :=
  ∀' ∃' ∀' ((memF 2 1) ⇔ ∀' ((memF 3 2) ⟹ (memF 3 0)))

/-- Infinity: there is a set containing the empty set and closed under `x ↦ x ∪ {x}`. -/
def infinityAx : setLang.Sentence :=
  ∃' ((∃' ((memF 1 0) ⊓ ∀' (∼ (memF 2 1)))) ⊓
    ∀' ((memF 1 0) ⟹ ∃' ((memF 2 0) ⊓ ∀' ((memF 3 2) ⇔ ((memF 3 1) ⊔ (eqF 3 1))))))

/-- Foundation. -/
def foundationAx : setLang.Sentence :=
  ∀' ((∃' (memF 1 0)) ⟹ ∃' ((memF 1 0) ⊓ ∀' ((memF 2 1) ⟹ ∼ (memF 2 0))))

/-- Choice, in the form: a set of pairwise disjoint nonempty sets has a transversal. -/
def choiceAx : setLang.Sentence :=
  ∀' ((((∀' ((memF 1 0) ⟹ ∃' (memF 2 1))) ⊓
      (∀' ∀' ((((memF 1 0) ⊓ (memF 2 0)) ⊓ ∃' ((memF 3 1) ⊓ (memF 3 2))) ⟹ (eqF 1 2))))) ⟹
    ∃' ∀' ((memF 2 0) ⟹ ∃' ((((memF 3 2) ⊓ (memF 3 1)) ⊓
      ∀' (((memF 4 2) ⊓ (memF 4 1)) ⟹ (eqF 4 3))))))

/-- The variable map used in the separation scheme: the separated variable goes to slot `k + 2`,
the parameters stay in slots `0, …, k - 1`. -/
def gSep (k : ℕ) : Fin (k + 1) → Fin (k + 3) := fun i =>
  if i.val = 0 then ⟨k + 2, by omega⟩ else ⟨i.val - 1, by omega⟩

/-- The instance of the separation scheme for the formula `φ`, whose free variable `0` is the
variable being separated and whose remaining free variables are parameters. -/
def sepAx {k : ℕ} (φ : setLang.Formula (Fin (k + 1))) : setLang.Sentence :=
  (∀' ∃' ∀' ((memF ⟨k + 2, by omega⟩ ⟨k + 1, by omega⟩) ⇔
      ((memF ⟨k + 2, by omega⟩ ⟨k, by omega⟩) ⊓ subst₀ φ (gSep k))) :
    setLang.BoundedFormula Empty k).alls

/-- Variable map for the first occurrence of `φ` in the replacement scheme. -/
def gRep₁ (k : ℕ) : Fin (k + 2) → Fin (k + 3) := fun i =>
  if i.val = 0 then ⟨k + 1, by omega⟩ else if i.val = 1 then ⟨k + 2, by omega⟩
  else ⟨i.val - 2, by omega⟩

/-- Variable map for the second occurrence of `φ` in the replacement scheme. -/
def gRep₂ (k : ℕ) : Fin (k + 2) → Fin (k + 4) := fun i =>
  if i.val = 0 then ⟨k + 1, by omega⟩ else if i.val = 1 then ⟨k + 3, by omega⟩
  else ⟨i.val - 2, by omega⟩

/-- Variable map for the third occurrence of `φ` in the replacement scheme. -/
def gRep₃ (k : ℕ) : Fin (k + 2) → Fin (k + 4) := fun i =>
  if i.val = 0 then ⟨k + 3, by omega⟩ else if i.val = 1 then ⟨k + 2, by omega⟩
  else ⟨i.val - 2, by omega⟩

/-- The instance of the replacement scheme for the formula `φ`, whose free variables `0` and `1`
are the arguments of the class function and whose remaining free variables are parameters. -/
def repAx {k : ℕ} (φ : setLang.Formula (Fin (k + 2))) : setLang.Sentence :=
  (∀' ((∀' ((memF ⟨k + 1, by omega⟩ ⟨k, by omega⟩) ⟹
        ∃' ((subst₀ φ (gRep₁ k)) ⊓
          ∀' ((subst₀ φ (gRep₂ k)) ⟹ (eqF ⟨k + 3, by omega⟩ ⟨k + 2, by omega⟩))))) ⟹
      ∃' ∀' ((memF ⟨k + 2, by omega⟩ ⟨k + 1, by omega⟩) ⇔
        ∃' ((memF ⟨k + 3, by omega⟩ ⟨k, by omega⟩) ⊓ subst₀ φ (gRep₃ k)))) :
    setLang.BoundedFormula Empty k).alls

/-- The theory `ZFC`, in the first-order language of set theory. -/
def ZFC : setLang.Theory :=
  {extensionalityAx, emptySetAx, pairingAx, unionAx, powerSetAx, infinityAx, foundationAx,
    choiceAx} ∪
  {ψ | ∃ (k : ℕ) (φ : setLang.Formula (Fin (k + 1))), ψ = sepAx φ} ∪
  {ψ | ∃ (k : ℕ) (φ : setLang.Formula (Fin (k + 2))), ψ = repAx φ}

/-! ### `ZFSet` is a model of `ZFC` -/

theorem zfSet_extensionality : ZFSet.{u} ⊨ extensionalityAx := by
  have key : ∀ x y : ZFSet.{u}, (∀ z, z ∈ x ↔ z ∈ y) → x = y := fun _ _ h => ZFSet.ext h
  simpa [extensionalityAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

theorem zfSet_emptySet : ZFSet.{u} ⊨ emptySetAx := by
  have key : ∃ x : ZFSet.{u}, ∀ y, ¬ y ∈ x := ⟨∅, by simp⟩
  simpa [emptySetAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

theorem zfSet_pairing : ZFSet.{u} ⊨ pairingAx := by
  have key : ∀ x y : ZFSet.{u}, ∃ z, ∀ w, w ∈ z ↔ (w = x ∨ w = y) :=
    fun x y => ⟨{x, y}, fun _ => ZFSet.mem_pair⟩
  simpa [pairingAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

theorem zfSet_union : ZFSet.{u} ⊨ unionAx := by
  have key : ∀ x : ZFSet.{u}, ∃ u, ∀ w, w ∈ u ↔ ∃ y, y ∈ x ∧ w ∈ y :=
    fun x => ⟨ZFSet.sUnion x, fun _ => by simp⟩
  simpa [unionAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

theorem zfSet_powerSet : ZFSet.{u} ⊨ powerSetAx := by
  have key : ∀ x : ZFSet.{u}, ∃ p, ∀ w, w ∈ p ↔ ∀ z, z ∈ w → z ∈ x :=
    fun x => ⟨x.powerset, fun _ => by
      rw [ZFSet.mem_powerset]; exact ⟨fun h _ hz => h hz, fun h _ hz => h _ hz⟩⟩
  simpa [powerSetAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

theorem zfSet_infinity : ZFSet.{u} ⊨ infinityAx := by
  have key : ∃ i : ZFSet.{u}, (∃ e, e ∈ i ∧ ∀ z, ¬ z ∈ e) ∧
      ∀ x, x ∈ i → ∃ s, s ∈ i ∧ ∀ w, w ∈ s ↔ (w ∈ x ∨ w = x) := by
    refine ⟨ZFSet.omega, ⟨∅, ZFSet.omega_zero, by simp⟩, fun x hx =>
      ⟨insert x x, ZFSet.omega_succ hx, fun w => ?_⟩⟩
    rw [ZFSet.mem_insert_iff]
    tauto
  simpa [infinityAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

theorem zfSet_foundation : ZFSet.{u} ⊨ foundationAx := by
  have key : ∀ x : ZFSet.{u}, (∃ y, y ∈ x) → ∃ y, y ∈ x ∧ ∀ z, z ∈ y → ¬ z ∈ x := by
    rintro x ⟨y, hy⟩
    have hx : x ≠ ∅ := by
      rintro rfl
      exact ZFSet.notMem_empty y hy
    obtain ⟨w, hw, hwe⟩ := ZFSet.regularity x hx
    refine ⟨w, hw, fun z hzw hzx => ?_⟩
    have : z ∈ x ∩ w := ZFSet.mem_inter.2 ⟨hzx, hzw⟩
    rw [hwe] at this
    exact ZFSet.notMem_empty z this
  simpa [foundationAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

attribute [local instance] Classical.allZFSetDefinable

theorem zfSet_choice : ZFSet.{u} ⊨ choiceAx := by
  have key : ∀ a : ZFSet.{u},
      ((∀ x : ZFSet.{u}, x ∈ a → ∃ z : ZFSet.{u}, z ∈ x) ∧
        (∀ x y : ZFSet.{u}, ((x ∈ a ∧ y ∈ a) ∧ ∃ z : ZFSet.{u}, z ∈ x ∧ z ∈ y) → x = y)) →
      ∃ c : ZFSet.{u}, ∀ x : ZFSet.{u}, x ∈ a → ∃ z : ZFSet.{u}, (z ∈ x ∧ z ∈ c) ∧
        ∀ w : ZFSet.{u}, (w ∈ x ∧ w ∈ c) → w = z := by
    rintro a ⟨hne, hdisj⟩
    obtain ⟨f, hfmem⟩ : ∃ f : ZFSet.{u} → ZFSet.{u}, ∀ x, x ∈ a → f x ∈ x := by
      refine ⟨fun x => if h : ∃ z, z ∈ x then h.choose else ∅, fun x hx => ?_⟩
      show dite (∃ z, z ∈ x) _ _ ∈ x
      rw [dif_pos (hne x hx)]
      exact (hne x hx).choose_spec
    refine ⟨ZFSet.image f a, fun x hx =>
      ⟨f x, ⟨hfmem x hx, ZFSet.mem_image.2 ⟨x, hx, rfl⟩⟩, ?_⟩⟩
    rintro w ⟨hwx, hwc⟩
    obtain ⟨y, hy, rfl⟩ := ZFSet.mem_image.1 hwc
    exact congrArg f (hdisj x y ⟨⟨hx, hy⟩, ⟨f y, hwx, hfmem y hy⟩⟩).symm
  simpa [choiceAx, Sentence.Realize, Formula.Realize, Fin.snoc] using key

theorem snoc3_gSep {k : ℕ} (xs : Fin k → ZFSet.{u}) (a b c : ZFSet.{u}) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c : Fin (k + 3) → ZFSet.{u}) ∘ gSep k
      = extVal₁ c xs := by
  funext i
  have hi := i.isLt
  by_cases h : (i : ℕ) = 0
  · simp only [Function.comp_apply, gSep, extVal₁, if_pos h, dif_pos h]
    exact snoc3_k2 _ _ _ _ _
  · simp only [Function.comp_apply, gSep, extVal₁, if_neg h, dif_neg h]
    exact snoc3_lt _ _ _ _ _ _ (by omega)

theorem zfSet_sep {k : ℕ} (φ : setLang.Formula (Fin (k + 1))) : ZFSet.{u} ⊨ sepAx φ := by
  simp only [sepAx, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, realize_memF, realize_subst₀]
  intro xs a
  refine ⟨ZFSet.sep (fun c => φ.Realize (extVal₁ c xs)) a, fun c => ?_⟩
  rw [snoc3_gSep, snoc3_k, snoc3_k1, snoc3_k2]
  exact ZFSet.mem_sep

theorem snoc3_gRep₁ {k : ℕ} (xs : Fin k → ZFSet.{u}) (a x y : ZFSet.{u}) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs a) x) y : Fin (k + 3) → ZFSet.{u}) ∘ gRep₁ k
      = extVal₂ x y xs := by
  funext i
  have hi := i.isLt
  by_cases h : (i : ℕ) = 0
  · simp only [Function.comp_apply, gRep₁, extVal₂, if_pos h, dif_pos h]
    exact snoc3_k1 _ _ _ _ _
  · by_cases h' : (i : ℕ) = 1
    · simp only [Function.comp_apply, gRep₁, extVal₂, if_neg h, dif_neg h, if_pos h', dif_pos h']
      exact snoc3_k2 _ _ _ _ _
    · simp only [Function.comp_apply, gRep₁, extVal₂, if_neg h, dif_neg h, if_neg h', dif_neg h']
      exact snoc3_lt _ _ _ _ _ _ (by omega)

theorem snoc4_gRep₂ {k : ℕ} (xs : Fin k → ZFSet.{u}) (a x y y' : ZFSet.{u}) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) x) y) y' : Fin (k + 4) → ZFSet.{u}) ∘ gRep₂ k
      = extVal₂ x y' xs := by
  funext i
  have hi := i.isLt
  by_cases h : (i : ℕ) = 0
  · simp only [Function.comp_apply, gRep₂, extVal₂, if_pos h, dif_pos h]
    exact snoc4_k1 _ _ _ _ _ _
  · by_cases h' : (i : ℕ) = 1
    · simp only [Function.comp_apply, gRep₂, extVal₂, if_neg h, dif_neg h, if_pos h', dif_pos h']
      exact snoc4_k3 _ _ _ _ _ _
    · simp only [Function.comp_apply, gRep₂, extVal₂, if_neg h, dif_neg h, if_neg h', dif_neg h']
      exact snoc4_lt _ _ _ _ _ _ _ (by omega)

theorem snoc4_gRep₃ {k : ℕ} (xs : Fin k → ZFSet.{u}) (a b y x : ZFSet.{u}) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) y) x : Fin (k + 4) → ZFSet.{u}) ∘ gRep₃ k
      = extVal₂ x y xs := by
  funext i
  have hi := i.isLt
  by_cases h : (i : ℕ) = 0
  · simp only [Function.comp_apply, gRep₃, extVal₂, if_pos h, dif_pos h]
    exact snoc4_k3 _ _ _ _ _ _
  · by_cases h' : (i : ℕ) = 1
    · simp only [Function.comp_apply, gRep₃, extVal₂, if_neg h, dif_neg h, if_pos h', dif_pos h']
      exact snoc4_k2 _ _ _ _ _ _
    · simp only [Function.comp_apply, gRep₃, extVal₂, if_neg h, dif_neg h, if_neg h', dif_neg h']
      exact snoc4_lt _ _ _ _ _ _ _ (by omega)

theorem zfSet_rep {k : ℕ} (φ : setLang.Formula (Fin (k + 2))) : ZFSet.{u} ⊨ repAx φ := by
  simp only [repAx, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, realize_memF, realize_eqF, realize_subst₀,
    snoc3_gRep₁, snoc4_gRep₂, snoc4_gRep₃, snoc2_k, snoc2_k1, snoc4_k]
  intro xs a hfun
  have hfun' : ∀ x : ZFSet.{u}, ∃ y : ZFSet.{u}, x ∈ a →
      (φ.Realize (extVal₂ x y xs) ∧ ∀ y', φ.Realize (extVal₂ x y' xs) → y' = y) := by
    intro x
    by_cases hx : x ∈ a
    · obtain ⟨y, hy⟩ := hfun x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose f hf using hfun'
  refine ⟨ZFSet.image f a, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := ZFSet.mem_image.1 hy
    exact ⟨x, hx, (hf x hx).1⟩
  · rintro ⟨x, hx, hP⟩
    exact ZFSet.mem_image.2 ⟨x, hx, ((hf x hx).2 y hP).symm⟩

/-- `ZFSet` is a model of `ZFC`. -/
instance zfSet_models_ZFC : ZFSet.{u} ⊨ ZFC := by
  refine ⟨?_⟩
  rintro ψ ((h | ⟨k, φ, rfl⟩) | ⟨k, φ, rfl⟩)
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact zfSet_extensionality
    · exact zfSet_emptySet
    · exact zfSet_pairing
    · exact zfSet_union
    · exact zfSet_powerSet
    · exact zfSet_infinity
    · exact zfSet_foundation
    · exact zfSet_choice
  · exact zfSet_sep φ
  · exact zfSet_rep φ

/-- `ZFC` is satisfiable, i.e. `Con(ZFC)` holds: `ZFSet` is a model. -/
theorem ZFC_isSatisfiable : ZFC.IsSatisfiable :=
  Language.Theory.Model.isSatisfiable ZFSet.{0}

/-- Any consistent extension of `ZFC` yields the consistency of `ZFC`; in particular, taking for
`T` a theory asserting the existence of an inaccessible cardinal,
`Con(ZFC + inaccessible) → Con(ZFC)`. -/
theorem ConZFC_of_extension_isSatisfiable (T : setLang.Theory) (h : (ZFC ∪ T).IsSatisfiable) :
    ZFC.IsSatisfiable :=
  h.mono Set.subset_union_left

/-- **Inaccessible implies Con(ZFC)**: if there is an inaccessible cardinal, then the
first-order theory `ZFC` has a model, i.e. `Con(ZFC)` holds.

The hypothesis is recorded because it is part of the requested statement; the proof does not
need it, since Mathlib's type `ZFSet` of ZFC-sets is outright a model of `ZFC`
(`Frontier.zfSet_models_ZFC`), Lean's type-theoretic universes playing the role of the
inaccessible cardinal. -/
theorem inaccessible_implies_ConZFC
    (_hIC : ∃ κ : Cardinal.{0}, κ.IsInaccessible) : ZFC.IsSatisfiable :=
  ZFC_isSatisfiable

/-! ### A sanity check: the axiomatization is not vacuous

The one-point structure in which `∈` always holds is *not* a model of `ZFC`; this rules out the
degenerate possibility that the sentences above are realized in every structure. -/

section Sanity

/-- The one-point structure in which every membership statement is true. -/
local instance trivialStructure : setLang.Structure Unit where
  funMap {_} f := Empty.elim f
  RelMap {n} r := match n, r with
    | 2, memRel.mem => fun _ => True

theorem trivial_not_models_emptySetAx : ¬ (Unit ⊨ emptySetAx) := by
  simp only [emptySetAx, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_all, BoundedFormula.realize_not, memF]
  simp [Structure.RelMap]

theorem trivial_not_models_ZFC : ¬ (Unit ⊨ ZFC) := by
  intro h
  exact trivial_not_models_emptySetAx
    (h.realize_of_mem emptySetAx (Or.inl (Or.inl (by simp))))

end Sanity

end Frontier

