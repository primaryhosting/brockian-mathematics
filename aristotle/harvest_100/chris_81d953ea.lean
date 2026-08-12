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
# Tarski's undefinability of truth

We formalize, from scratch, the statement that arithmetical truth is not arithmetically
definable.

* `Frontier.ATerm` / `Frontier.AFormula` : the syntax of first-order arithmetic
  (variables indexed by `ℕ`, a constant for each natural number, `+`, `*`, `=`, `¬`, `∧`, `∃`).
* `Frontier.Sat` : satisfaction in the standard model `ℕ`.
* `Frontier.IsSentence` : having no free variables.
* `Frontier.encodeF` : an injective Gödel numbering of formulas (`Frontier.encodeF_inj`).
* `Frontier.TrueArith` : the set of Gödel numbers of true arithmetical sentences.
* `Frontier.ArithDefinable` : a set of naturals is definable by an arithmetical formula.
* `Frontier.no_truth_predicate` : no formula satisfies the Tarski biconditionals.
* `Frontier.Tarski_undefinability` : `¬ ArithDefinable TrueArith`.

The key step is the diagonal construction: for a formula `p` with a single free variable,
the sentence `sub1 p m` is `∃ v₀, v₀ = m ∧ p`, which says that `p` holds of `m`. Because the
Gödel numbering is built from the polynomial pairing function `Frontier.pr`, the code of
`sub1 p m` is a *polynomial* in the code of `p` and in `m` (`Frontier.encodeF_sub1`), so the
diagonal function `a ↦ encodeF (sub1 p a)` (for `a = encodeF p`) is computed by an explicit
term `Frontier.diagTerm` of the language itself. No further arithmetization is needed.

The last section (`Frontier.ArithDefinable_pure`) shows that the constants for all natural
numbers are eliminable: every definable set is defined by a formula whose only constants are
`0` and `1`, i.e. a formula of the usual language `{0, 1, +, ·}` of arithmetic.
-/

namespace Frontier

/-! ## A polynomial pairing function -/

/-- An injective polynomial pairing function on `ℕ`. -/
def pr (x y : ℕ) : ℕ := (x + y) * (x + y) + x

theorem pr_inj {a b c d : ℕ} (h : pr a b = pr c d) : a = c ∧ b = d := by
  have key : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | he | hgt
    · exfalso
      have h1 : a + b + 1 ≤ c + d := hlt
      have h2 : (a + b + 1) * (a + b + 1) ≤ (c + d) * (c + d) := Nat.mul_le_mul h1 h1
      have h3 : a ≤ a + b := Nat.le_add_right a b
      simp only [pr] at h
      nlinarith
    · exact he
    · exfalso
      have h1 : c + d + 1 ≤ a + b := hgt
      have h2 : (c + d + 1) * (c + d + 1) ≤ (a + b) * (a + b) := Nat.mul_le_mul h1 h1
      have h3 : c ≤ c + d := Nat.le_add_right c d
      simp only [pr] at h
      nlinarith
  have ha : a = c := by
    simp only [pr, key] at h
    exact Nat.add_left_cancel h
  exact ⟨ha, by omega⟩

/-! ## Syntax -/

/-- Terms of the language of arithmetic: variables `v i` (`i : ℕ`), a constant for every
natural number, addition and multiplication. -/
inductive ATerm : Type
  | var : ℕ → ATerm
  | num : ℕ → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq

/-- Formulas of the language of arithmetic: equations between terms, negation, conjunction
and existential quantification. -/
inductive AFormula : Type
  | eqf : ATerm → ATerm → AFormula
  | neg : AFormula → AFormula
  | conj : AFormula → AFormula → AFormula
  | ex : ℕ → AFormula → AFormula
  deriving DecidableEq

/-! ## Semantics in the standard model `ℕ` -/

/-- Value of a term under an assignment of natural numbers to the variables. -/
def evalT : ATerm → (ℕ → ℕ) → ℕ
  | .var i, v => v i
  | .num n, _ => n
  | .add t u, v => evalT t v + evalT u v
  | .mul t u, v => evalT t v * evalT u v

/-- Satisfaction of a formula in the standard model `ℕ` under an assignment. -/
def Sat : AFormula → (ℕ → ℕ) → Prop
  | .eqf t u, v => evalT t v = evalT u v
  | .neg p, v => ¬ Sat p v
  | .conj p q, v => Sat p v ∧ Sat q v
  | .ex i p, v => ∃ n : ℕ, Sat p (Function.update v i n)

/-- The variables occurring in a term. -/
def varsT : ATerm → Finset ℕ
  | .var i => {i}
  | .num _ => ∅
  | .add t u => varsT t ∪ varsT u
  | .mul t u => varsT t ∪ varsT u

/-- The free variables of a formula. -/
def freeVars : AFormula → Finset ℕ
  | .eqf t u => varsT t ∪ varsT u
  | .neg p => freeVars p
  | .conj p q => freeVars p ∪ freeVars q
  | .ex i p => (freeVars p).erase i

/-- A sentence is a formula without free variables. -/
def IsSentence (p : AFormula) : Prop := freeVars p = ∅

/-! ## Gödel numbering -/

/-- Gödel numbering of terms. -/
def encodeT : ATerm → ℕ
  | .var i => pr 1 i
  | .num n => pr 2 n
  | .add t u => pr 3 (pr (encodeT t) (encodeT u))
  | .mul t u => pr 4 (pr (encodeT t) (encodeT u))

/-- Gödel numbering of formulas. -/
def encodeF : AFormula → ℕ
  | .eqf t u => pr 0 (pr (encodeT t) (encodeT u))
  | .neg p => pr 1 (encodeF p)
  | .conj p q => pr 2 (pr (encodeF p) (encodeF q))
  | .ex i p => pr 3 (pr i (encodeF p))

theorem encodeT_inj : ∀ {t u : ATerm}, encodeT t = encodeT u → t = u := by
  intro t
  induction t with
  | var i =>
      intro u h; cases u <;> simp only [encodeT] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h; simp [h2])
  | num n =>
      intro u h; cases u <;> simp only [encodeT] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h; simp [h2])
  | add t1 t2 ih1 ih2 =>
      intro u h; cases u <;> simp only [encodeT] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h
           obtain ⟨h3, h4⟩ := pr_inj h2
           simp [ih1 h3, ih2 h4])
  | mul t1 t2 ih1 ih2 =>
      intro u h; cases u <;> simp only [encodeT] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h
           obtain ⟨h3, h4⟩ := pr_inj h2
           simp [ih1 h3, ih2 h4])

theorem encodeF_inj : ∀ {p q : AFormula}, encodeF p = encodeF q → p = q := by
  intro p
  induction p with
  | eqf t u =>
      intro q h; cases q <;> simp only [encodeF] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h
           obtain ⟨h3, h4⟩ := pr_inj h2
           simp [encodeT_inj h3, encodeT_inj h4])
  | neg p ih =>
      intro q h; cases q <;> simp only [encodeF] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h; simp [ih h2])
  | conj p1 p2 ih1 ih2 =>
      intro q h; cases q <;> simp only [encodeF] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h
           obtain ⟨h3, h4⟩ := pr_inj h2
           simp [ih1 h3, ih2 h4])
  | ex i p ih =>
      intro q h; cases q <;> simp only [encodeF] at h <;>
        first
        | (obtain ⟨h1, -⟩ := pr_inj h; omega)
        | (obtain ⟨-, h2⟩ := pr_inj h
           obtain ⟨h3, h4⟩ := pr_inj h2
           simp [h3, ih h4])

/-! ## The truth set and definability -/

/-- The set of Gödel numbers of arithmetical sentences true in the standard model. -/
def TrueArith : Set ℕ :=
  {n | ∃ s : AFormula, IsSentence s ∧ encodeF s = n ∧ Sat s (fun _ => 0)}

/-- A set of natural numbers is arithmetically definable if it is the extension, in the
standard model, of an arithmetical formula in the single free variable `v 0`. -/
def ArithDefinable (S : Set ℕ) : Prop :=
  ∃ p : AFormula, freeVars p ⊆ {0} ∧ ∀ n : ℕ, n ∈ S ↔ Sat p (fun _ => n)

/-! ## Coincidence lemmas -/

theorem evalT_congr : ∀ (t : ATerm) {v w : ℕ → ℕ}, (∀ i ∈ varsT t, v i = w i) →
    evalT t v = evalT t w := by
  intro t
  induction t with
  | var i => intro v w h; exact h i (by simp [varsT])
  | num n => intro v w _; rfl
  | add t u iht ihu =>
      intro v w h
      simp only [evalT]
      rw [iht (fun i hi => h i (by simp [varsT, hi])),
        ihu (fun i hi => h i (by simp [varsT, hi]))]
  | mul t u iht ihu =>
      intro v w h
      simp only [evalT]
      rw [iht (fun i hi => h i (by simp [varsT, hi])),
        ihu (fun i hi => h i (by simp [varsT, hi]))]

theorem Sat_congr : ∀ (p : AFormula) {v w : ℕ → ℕ}, (∀ i ∈ freeVars p, v i = w i) →
    (Sat p v ↔ Sat p w) := by
  intro p
  induction p with
  | eqf t u =>
      intro v w h
      simp only [Sat]
      rw [evalT_congr t (fun i hi => h i (by simp [freeVars, hi])),
        evalT_congr u (fun i hi => h i (by simp [freeVars, hi]))]
  | neg p ih => intro v w h; simp only [Sat]; rw [ih h]
  | conj p q ihp ihq =>
      intro v w h
      simp only [Sat]
      rw [ihp (fun i hi => h i (by simp [freeVars, hi])),
        ihq (fun i hi => h i (by simp [freeVars, hi]))]
  | ex i p ih =>
      intro v w h
      simp only [Sat]
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨n, (ih ?_).mp hn⟩
        intro j hj
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Function.update_of_ne hji]
          exact h j (by simp [freeVars, Finset.mem_erase, hji, hj])
      · rintro ⟨n, hn⟩
        refine ⟨n, (ih ?_).mpr hn⟩
        intro j hj
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Function.update_of_ne hji]
          exact h j (by simp [freeVars, Finset.mem_erase, hji, hj])

/-! ## Substitution of a term for a variable -/

/-- Substitution of a term for a variable in a term. -/
def substT (k : ℕ) (s : ATerm) : ATerm → ATerm
  | .var i => if i = k then s else .var i
  | .num n => .num n
  | .add t u => .add (substT k s t) (substT k s u)
  | .mul t u => .mul (substT k s t) (substT k s u)

/-- Substitution of a term for the free occurrences of a variable in a formula. -/
def substF (k : ℕ) (s : ATerm) : AFormula → AFormula
  | .eqf t u => .eqf (substT k s t) (substT k s u)
  | .neg p => .neg (substF k s p)
  | .conj p q => .conj (substF k s p) (substF k s q)
  | .ex i p => if i = k then .ex i p else .ex i (substF k s p)

theorem evalT_substT (k : ℕ) (s : ATerm) : ∀ (t : ATerm) (v : ℕ → ℕ),
    evalT (substT k s t) v = evalT t (Function.update v k (evalT s v)) := by
  intro t
  induction t with
  | var i =>
      intro v
      by_cases h : i = k
      · subst h; simp [substT, evalT]
      · simp [substT, evalT, h]
  | num n => intro v; rfl
  | add t u iht ihu => intro v; simp only [substT, evalT, iht, ihu]
  | mul t u iht ihu => intro v; simp only [substT, evalT, iht, ihu]

theorem Sat_substF (k : ℕ) (s : ATerm) (hs : varsT s ⊆ {k}) : ∀ (p : AFormula) (v : ℕ → ℕ),
    (Sat (substF k s p) v ↔ Sat p (Function.update v k (evalT s v))) := by
  intro p
  induction p with
  | eqf t u => intro v; simp only [substF, Sat, evalT_substT]
  | neg p ih => intro v; simp only [substF, Sat, ih]
  | conj p q ihp ihq => intro v; simp only [substF, Sat, ihp, ihq]
  | ex i p ih =>
      intro v
      by_cases hik : i = k
      · subst hik
        simp only [substF, Sat]
        constructor
        · rintro ⟨n, hn⟩
          exact ⟨n, by rwa [Function.update_idem]⟩
        · rintro ⟨n, hn⟩
          rw [Function.update_idem] at hn
          exact ⟨n, hn⟩
      · have hki : k ≠ i := fun h => hik h.symm
        have hev : ∀ n : ℕ, evalT s (Function.update v i n) = evalT s v := by
          intro n
          refine evalT_congr s ?_
          intro j hj
          have hjk : j = k := by simpa using hs hj
          subst hjk
          exact Function.update_of_ne hki _ _
        simp only [substF, if_neg hik, Sat]
        constructor
        · rintro ⟨n, hn⟩
          rw [ih, hev, Function.update_comm hik] at hn
          exact ⟨n, hn⟩
        · rintro ⟨n, hn⟩
          refine ⟨n, ?_⟩
          rw [ih, hev, Function.update_comm hik]
          exact hn

theorem varsT_substT (k : ℕ) (s : ATerm) : ∀ t : ATerm,
    varsT (substT k s t) ⊆ (varsT t).erase k ∪ varsT s := by
  intro t
  induction t with
  | var i =>
      by_cases h : i = k
      · subst h; simp [substT, varsT]
      · simp only [substT, if_neg h, varsT]
        intro j hj
        simp only [Finset.mem_singleton] at hj
        subst hj
        simp [Finset.mem_union, Finset.mem_erase, h]
  | num n => simp [substT, varsT]
  | add t u iht ihu =>
      simp only [substT, varsT]
      intro j hj
      simp only [Finset.mem_union] at hj
      rcases hj with hj | hj
      · have := iht hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
      · have := ihu hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
  | mul t u iht ihu =>
      simp only [substT, varsT]
      intro j hj
      simp only [Finset.mem_union] at hj
      rcases hj with hj | hj
      · have := iht hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
      · have := ihu hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto

theorem freeVars_substF (k : ℕ) (s : ATerm) : ∀ p : AFormula,
    freeVars (substF k s p) ⊆ (freeVars p).erase k ∪ varsT s := by
  intro p
  induction p with
  | eqf t u =>
      simp only [substF, freeVars]
      intro j hj
      simp only [Finset.mem_union] at hj
      rcases hj with hj | hj
      · have := varsT_substT k s t hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
      · have := varsT_substT k s u hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
  | neg p ih => simpa [substF, freeVars] using ih
  | conj p q ihp ihq =>
      simp only [substF, freeVars]
      intro j hj
      simp only [Finset.mem_union] at hj
      rcases hj with hj | hj
      · have := ihp hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
      · have := ihq hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
  | ex i p ih =>
      by_cases hik : i = k
      · subst hik
        have hid : substF i s (AFormula.ex i p) = AFormula.ex i p := by simp [substF]
        rw [hid]
        intro j hj
        simp only [freeVars, Finset.mem_erase] at hj
        simp only [freeVars, Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨hj.1, hj.1, hj.2⟩
      · simp only [substF, if_neg hik, freeVars]
        intro j hj
        simp only [Finset.mem_erase] at hj
        have := ih hj.2
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        rcases this with h | h
        · exact Or.inl ⟨h.1, hj.1, h.2⟩
        · exact Or.inr h

/-! ## The diagonal construction -/

/-- `sub1 p m` is the formula `∃ v₀, v₀ = m ∧ p`, i.e. `p` with the numeral `m` plugged into
its free variable `v 0`. -/
def sub1 (p : AFormula) (m : ℕ) : AFormula :=
  .ex 0 (.conj (.eqf (.var 0) (.num m)) p)

/-- The arithmetic function computing the code of `sub1 p m` from the code of `p` and `m`.
It is a polynomial in both arguments. -/
def G (a m : ℕ) : ℕ := pr 3 (pr 0 (pr 2 (pr (pr 0 (pr (pr 1 0) (pr 2 m))) a)))

theorem encodeF_sub1 (p : AFormula) (m : ℕ) : encodeF (sub1 p m) = G (encodeF p) m := rfl

/-- The term-level pairing function. -/
def prT (t u : ATerm) : ATerm := .add (.mul (.add t u) (.add t u)) t

theorem evalT_prT (t u : ATerm) (v : ℕ → ℕ) :
    evalT (prT t u) v = pr (evalT t v) (evalT u v) := rfl

/-- A term, in the single variable `v 0`, whose value is the code of the diagonalization
`sub1 p (encodeF p)` when `v 0` is the code of `p`. -/
def diagTerm : ATerm :=
  prT (.num 3) (prT (.num 0) (prT (.num 2)
    (prT (prT (.num 0) (prT (prT (.num 1) (.num 0)) (prT (.num 2) (.var 0)))) (.var 0))))

theorem evalT_diagTerm (v : ℕ → ℕ) : evalT diagTerm v = G (v 0) (v 0) := rfl

theorem varsT_diagTerm : varsT diagTerm ⊆ {0} := by
  intro j hj
  simp only [diagTerm, prT, varsT, Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty, false_or, or_false] at hj ⊢
  tauto

theorem sat_sub1 (p : AFormula) (m : ℕ) (v : ℕ → ℕ) :
    Sat (sub1 p m) v ↔ Sat p (Function.update v 0 m) := by
  simp only [sub1, Sat, evalT]
  constructor
  · rintro ⟨n, hn, hp⟩
    simp only [Function.update_self] at hn
    subst hn
    exact hp
  · intro h
    exact ⟨m, by simp, h⟩

theorem isSentence_sub1 {p : AFormula} (h : freeVars p ⊆ {0}) (m : ℕ) :
    IsSentence (sub1 p m) := by
  have hE : freeVars (sub1 p m) = ∅ := by
    ext j
    simp only [sub1, freeVars, varsT, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, or_false, iff_false, not_and]
    intro hj0 hmem
    rcases hmem with hmem | hmem
    · exact hj0 hmem
    · exact hj0 (by simpa using h hmem)
  exact hE

/-! ## Tarski's theorem -/

/-- **Tarski's theorem, T-schema form**: there is no arithmetical formula `T` in the single
free variable `v 0` satisfying the Tarski biconditional `T(⌜s⌝) ↔ s` for every arithmetical
sentence `s`. -/
theorem no_truth_predicate :
    ¬ ∃ T : AFormula, freeVars T ⊆ {0} ∧
      ∀ s : AFormula, IsSentence s → (Sat T (fun _ => encodeF s) ↔ Sat s (fun _ => 0)) := by
  rintro ⟨T, hT0, hT⟩
  -- the diagonal formula `dg(v₀) := ¬ T(diagTerm(v₀))`
  let dg : AFormula := .neg (substF 0 diagTerm T)
  have hdgfree : freeVars dg ⊆ {0} := by
    have h1 : freeVars dg ⊆ (freeVars T).erase 0 ∪ varsT diagTerm :=
      freeVars_substF 0 diagTerm T
    refine h1.trans ?_
    intro j hj
    simp only [Finset.mem_union, Finset.mem_erase] at hj
    rcases hj with ⟨hj0, hjT⟩ | hj
    · have hj1 : j ∈ ({0} : Finset ℕ) := hT0 hjT
      simp only [Finset.mem_singleton] at hj1
      exact absurd hj1 hj0
    · exact varsT_diagTerm hj
  set p : ℕ := encodeF dg with hp
  let sn : AFormula := sub1 dg p
  have hsent : IsSentence sn := isSentence_sub1 hdgfree p
  have hcode : encodeF sn = G p p := encodeF_sub1 dg p
  have hsat : ∀ v : ℕ → ℕ, Sat sn v ↔ ¬ Sat T (fun _ => G p p) := by
    intro v
    show Sat (sub1 dg p) v ↔ _
    rw [sat_sub1]
    have h1 : Sat dg (Function.update v 0 p) ↔
        ¬ Sat T (Function.update (Function.update v 0 p) 0
          (evalT diagTerm (Function.update v 0 p))) := by
      show (¬ Sat (substF 0 diagTerm T) (Function.update v 0 p)) ↔ _
      rw [Sat_substF 0 diagTerm varsT_diagTerm]
    rw [h1, evalT_diagTerm]
    simp only [Function.update_self, Function.update_idem]
    have h2 : Sat T (Function.update v 0 (G p p)) ↔ Sat T (fun _ => G p p) := by
      refine Sat_congr T ?_
      intro i hi
      have : i = 0 := by simpa using hT0 hi
      subst this
      simp
    rw [h2]
  have h1 : Sat sn (fun _ => 0) ↔ ¬ Sat T (fun _ => encodeF sn) := by
    rw [hcode]; exact hsat _
  have h2 : Sat T (fun _ => encodeF sn) ↔ Sat sn (fun _ => 0) := hT sn hsent
  tauto

/-- **Tarski's undefinability of truth**: the set of Gödel numbers of true sentences of
arithmetic is not definable by any formula of arithmetic (interpreted in the standard
model `ℕ`). -/
theorem Tarski_undefinability : ¬ ArithDefinable TrueArith := by
  rintro ⟨T, hT0, hT⟩
  refine no_truth_predicate ⟨T, hT0, fun s hs => ?_⟩
  rw [← hT (encodeF s)]
  constructor
  · rintro ⟨t, -, ht, hsatt⟩
    have : t = s := encodeF_inj ht
    subst this
    exact hsatt
  · intro h
    exact ⟨s, hs, rfl, h⟩

/-! ## Sanity checks: the notions above are not vacuous -/

/-- The sentence `0 = 0` is true, so the truth set is nonempty. -/
example : encodeF (.eqf (.num 0) (.num 0)) ∈ TrueArith :=
  ⟨.eqf (.num 0) (.num 0), rfl, rfl, rfl⟩

/-- The sentence `0 = 1` is false, so not every code lies in the truth set. -/
example : encodeF (.eqf (.num 0) (.num 1)) ∉ TrueArith := by
  rintro ⟨t, -, ht, hsatt⟩
  have : t = AFormula.eqf (.num 0) (.num 1) := encodeF_inj ht
  subst this
  exact absurd hsatt (by simp [Sat, evalT])

/-- The set of even numbers is arithmetically definable: it is defined by `∃ v₁, v₀ = v₁ + v₁`.
This shows that `ArithDefinable` is not vacuous. -/
example : ArithDefinable {n : ℕ | ∃ k, n = 2 * k} := by
  refine ⟨.ex 1 (.eqf (.var 0) (.add (.var 1) (.var 1))), ?_, ?_⟩
  · intro j hj
    simp only [freeVars, varsT, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hj
    simp only [Finset.mem_singleton]
    omega
  · intro n
    simp only [Set.mem_setOf_eq, Sat, evalT, Function.update_self,
      Function.update_of_ne (by norm_num : (0 : ℕ) ≠ 1)]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ring⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by omega⟩

/-! ## The numeral constants are eliminable

Our language has a constant for every natural number. This section shows that this is
harmless: every definable set is already defined by a formula whose only constants are
`0` and `1`, i.e. a formula of the usual language `{0, 1, +, ·}` of arithmetic. -/

/-- The canonical term `((0 + 1) + 1) + ⋯ + 1` denoting `n`, using only the constants
`0` and `1`. -/
def numeral : ℕ → ATerm
  | 0 => .num 0
  | (n + 1) => .add (numeral n) (.num 1)

theorem evalT_numeral (n : ℕ) (v : ℕ → ℕ) : evalT (numeral n) v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [numeral, evalT, ih]

theorem varsT_numeral (n : ℕ) : varsT (numeral n) = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, varsT, ih]

/-- A term is *pure* if the only constants occurring in it are `0` and `1`. -/
def IsPureT : ATerm → Prop
  | .var _ => True
  | .num n => n ≤ 1
  | .add t u => IsPureT t ∧ IsPureT u
  | .mul t u => IsPureT t ∧ IsPureT u

/-- A formula is *pure* if the only constants occurring in it are `0` and `1`. -/
def IsPureF : AFormula → Prop
  | .eqf t u => IsPureT t ∧ IsPureT u
  | .neg p => IsPureF p
  | .conj p q => IsPureF p ∧ IsPureF q
  | .ex _ p => IsPureF p

theorem isPureT_numeral (n : ℕ) : IsPureT (numeral n) := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ n ih => exact ⟨ih, le_rfl⟩

/-- Replace every numeral constant in a term by its canonical `0`/`1` representation. -/
def pureT : ATerm → ATerm
  | .var i => .var i
  | .num n => numeral n
  | .add t u => .add (pureT t) (pureT u)
  | .mul t u => .mul (pureT t) (pureT u)

/-- Replace every numeral constant in a formula by its canonical `0`/`1` representation. -/
def pureF : AFormula → AFormula
  | .eqf t u => .eqf (pureT t) (pureT u)
  | .neg p => .neg (pureF p)
  | .conj p q => .conj (pureF p) (pureF q)
  | .ex i p => .ex i (pureF p)

theorem evalT_pureT : ∀ (t : ATerm) (v : ℕ → ℕ), evalT (pureT t) v = evalT t v := by
  intro t
  induction t with
  | var i => intro v; rfl
  | num n => intro v; exact evalT_numeral n v
  | add t u iht ihu => intro v; simp only [pureT, evalT, iht, ihu]
  | mul t u iht ihu => intro v; simp only [pureT, evalT, iht, ihu]

theorem varsT_pureT : ∀ t : ATerm, varsT (pureT t) = varsT t := by
  intro t
  induction t with
  | var i => rfl
  | num n => simpa [pureT, varsT] using varsT_numeral n
  | add t u iht ihu => simp only [pureT, varsT, iht, ihu]
  | mul t u iht ihu => simp only [pureT, varsT, iht, ihu]

theorem isPureT_pureT : ∀ t : ATerm, IsPureT (pureT t) := by
  intro t
  induction t with
  | var i => exact trivial
  | num n => exact isPureT_numeral n
  | add t u iht ihu => exact ⟨iht, ihu⟩
  | mul t u iht ihu => exact ⟨iht, ihu⟩

theorem Sat_pureF : ∀ (p : AFormula) (v : ℕ → ℕ), Sat (pureF p) v ↔ Sat p v := by
  intro p
  induction p with
  | eqf t u => intro v; simp only [pureF, Sat, evalT_pureT]
  | neg p ih => intro v; simp only [pureF, Sat, ih]
  | conj p q ihp ihq => intro v; simp only [pureF, Sat, ihp, ihq]
  | ex i p ih => intro v; simp only [pureF, Sat, ih]

theorem freeVars_pureF : ∀ p : AFormula, freeVars (pureF p) = freeVars p := by
  intro p
  induction p with
  | eqf t u => simp only [pureF, freeVars, varsT_pureT]
  | neg p ih => simp only [pureF, freeVars, ih]
  | conj p q ihp ihq => simp only [pureF, freeVars, ihp, ihq]
  | ex i p ih => simp only [pureF, freeVars, ih]

theorem isPureF_pureF : ∀ p : AFormula, IsPureF (pureF p) := by
  intro p
  induction p with
  | eqf t u => exact ⟨isPureT_pureT t, isPureT_pureT u⟩
  | neg p ih => exact ih
  | conj p q ihp ihq => exact ⟨ihp, ihq⟩
  | ex i p ih => exact ih

/-- Every arithmetically definable set is defined by a formula using only the constants
`0` and `1`; so the numerals in the language do not enlarge the class of definable sets. -/
theorem ArithDefinable_pure {S : Set ℕ} (h : ArithDefinable S) :
    ∃ p : AFormula, IsPureF p ∧ freeVars p ⊆ {0} ∧ ∀ n : ℕ, n ∈ S ↔ Sat p (fun _ => n) := by
  obtain ⟨q, hq0, hq⟩ := h
  refine ⟨pureF q, isPureF_pureF q, ?_, ?_⟩
  · rw [freeVars_pureF]; exact hq0
  · intro n; rw [Sat_pureF]; exact hq n

/-- Tarski's theorem for the pure language `{0, 1, +, ·}` of arithmetic: arithmetical truth
is not defined by any formula whose only constants are `0` and `1` either. -/
theorem Tarski_undefinability_pure :
    ¬ ∃ p : AFormula, IsPureF p ∧ freeVars p ⊆ {0} ∧
      ∀ n : ℕ, n ∈ TrueArith ↔ Sat p (fun _ => n) := by
  rintro ⟨p, -, hp0, hp⟩
  exact Tarski_undefinability ⟨p, hp0, hp⟩

end Frontier

