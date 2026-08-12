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
# Löb's theorem

This file gives a self-contained formalization of the syntax of first-order arithmetic,
of the theory `PA` (Peano arithmetic) together with a Hilbert-style proof calculus, of
Gödel numbering of formulas, of the box modality `□φ = Pr(⌜φ⌝)` attached to a provability
predicate `Pr`, and a proof of **Löb's theorem**:

> if `PA ⊩ □φ → φ` then `PA ⊩ φ`.

Everything used in the statement is defined here from scratch: terms, formulas,
substitution, the axioms of `PA`, the provability relation `PA ⊩ ·`, the Gödel numbering
`⌜·⌝`, numerals and the box modality.

The three Hilbert–Bernays–Löb derivability conditions and the diagonal (fixed point)
lemma are *hypotheses* of the theorem, packaged in the structure
`Frontier.ProvabilityPredicate`.  These are exactly the properties of the standard
`Σ₁` provability predicate of `PA` whose verification is the (purely arithmetical)
arithmetization of syntax; they are not proved here.  Löb's theorem is precisely the
statement that they *imply* `PA ⊩ □φ → φ  ⟹  PA ⊢ φ`.

That the hypotheses are consistent (so that the theorem is not vacuous) is witnessed by
`Frontier.ProvabilityPredicate.nonempty`.  As sanity checks on the definitions we also
prove that the Gödel numbering is injective (`Frontier.quote_injective`) and that the
calculus is sound for the standard model (`Frontier.Provable.sound`), hence consistent
(`Frontier.PA_consistent`).
-/

namespace Frontier

/-! ## Syntax of first-order arithmetic -/

/-- Terms of the language of arithmetic `{0, S, +, ·}`.  Variables are de Bruijn indices. -/
inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  deriving DecidableEq

/-- Formulas of the language of arithmetic, with primitive connectives `⊥`, `→` and `∀`
(de Bruijn style: `all p` binds the variable with index `0` in `p`). -/
inductive Formula where
  /-- An equation `t = u` between terms. -/
  | eq : Term → Term → Formula
  /-- Falsity. -/
  | bot : Formula
  /-- Implication. -/
  | imp : Formula → Formula → Formula
  /-- Universal quantification over the de Bruijn variable `0`. -/
  | all : Formula → Formula
  deriving DecidableEq

@[inherit_doc] infixr:26 " ⟶ " => Formula.imp

/-- Negation. -/
def Formula.neg (p : Formula) : Formula := p ⟶ Formula.bot

/-- Conjunction, defined from `⊥` and `→`. -/
def Formula.and (p q : Formula) : Formula := (p ⟶ q ⟶ Formula.bot) ⟶ Formula.bot

/-- Biconditional. -/
def Formula.iff (p q : Formula) : Formula := Formula.and (p ⟶ q) (q ⟶ p)

/-! ### Substitution -/

/-- Simultaneous substitution in terms. -/
def Term.subst (σ : ℕ → Term) : Term → Term
  | .var n => σ n
  | .zero => .zero
  | .succ t => .succ (t.subst σ)
  | .add t u => .add (t.subst σ) (u.subst σ)
  | .mul t u => .mul (t.subst σ) (u.subst σ)

/-- Shifting all de Bruijn indices up by one. -/
def Term.shift (t : Term) : Term := t.subst (fun n => .var (n + 1))

/-- Lifting a substitution under a binder. -/
def liftSubst (σ : ℕ → Term) : ℕ → Term
  | 0 => .var 0
  | n + 1 => (σ n).shift

/-- Simultaneous substitution in formulas. -/
def Formula.subst (σ : ℕ → Term) : Formula → Formula
  | .eq t u => .eq (t.subst σ) (u.subst σ)
  | .bot => .bot
  | .imp p q => .imp (p.subst σ) (q.subst σ)
  | .all p => .all (p.subst (liftSubst σ))

/-- The substitution replacing the variable `0` by `t` and decreasing all other indices. -/
def substOne (t : Term) : ℕ → Term
  | 0 => t
  | n + 1 => .var n

/-- Instantiation of the outermost bound variable of `p` by the term `t`. -/
def Formula.inst (p : Formula) (t : Term) : Formula := p.subst (substOne t)

/-- Shifting all de Bruijn indices of a formula up by one. -/
def Formula.shift (p : Formula) : Formula := p.subst (fun n => .var (n + 1))

/-- Substituting `S x` for the variable `x` with index `0`. -/
def Formula.instSucc (p : Formula) : Formula :=
  p.subst (fun n => match n with | 0 => .succ (.var 0) | (n + 1) => .var (n + 1))

/-! ### Propositional tautologies -/

/-- Propositional evaluation of a formula: atomic formulas (equations and universally
quantified formulas) are given truth values by `v`, the connectives `⊥` and `→` are
interpreted truth-functionally. -/
def Formula.pEval (v : Formula → Bool) : Formula → Bool
  | .eq t u => v (.eq t u)
  | .bot => false
  | .imp p q => !(p.pEval v) || q.pEval v
  | .all p => v (.all p)

/-- A formula is a *propositional tautology* if it evaluates to `true` under every
assignment of truth values to its atomic subformulas. -/
def Tautology (p : Formula) : Prop := ∀ v : Formula → Bool, p.pEval v = true

/-! ## The theory `PA` and its proof calculus -/

/-- The axioms of Peano arithmetic (over a Hilbert-style calculus for classical
first-order logic with equality, whose propositional part is given by all propositional
tautologies). -/
inductive PAaxiom : Formula → Prop
  /-- Every propositional tautology is an axiom. -/
  | taut {p : Formula} : Tautology p → PAaxiom p
  /-- Universal instantiation. -/
  | instantiate (p : Formula) (t : Term) : PAaxiom (.all p ⟶ p.inst t)
  /-- Distribution of `∀` over `→`. -/
  | allImp (p q : Formula) : PAaxiom (.all (p ⟶ q) ⟶ (.all p ⟶ .all q))
  /-- Vacuous quantification. -/
  | vacuous (p : Formula) : PAaxiom (p ⟶ .all p.shift)
  /-- Reflexivity of equality. -/
  | eqRefl (t : Term) : PAaxiom (.eq t t)
  /-- Leibniz' law. -/
  | eqSubst (p : Formula) (t u : Term) : PAaxiom (.eq t u ⟶ (p.inst t ⟶ p.inst u))
  /-- `∀x. S x ≠ 0`. -/
  | succNeZero : PAaxiom (.all (Formula.neg (.eq (.succ (.var 0)) .zero)))
  /-- `∀x ∀y. S x = S y → x = y`. -/
  | succInj : PAaxiom (.all (.all (.eq (.succ (.var 1)) (.succ (.var 0)) ⟶
      .eq (.var 1) (.var 0))))
  /-- `∀x. x + 0 = x`. -/
  | addZero : PAaxiom (.all (.eq (.add (.var 0) .zero) (.var 0)))
  /-- `∀x ∀y. x + S y = S (x + y)`. -/
  | addSucc : PAaxiom (.all (.all (.eq (.add (.var 1) (.succ (.var 0)))
      (.succ (.add (.var 1) (.var 0))))))
  /-- `∀x. x · 0 = 0`. -/
  | mulZero : PAaxiom (.all (.eq (.mul (.var 0) .zero) .zero))
  /-- `∀x ∀y. x · S y = x · y + x`. -/
  | mulSucc : PAaxiom (.all (.all (.eq (.mul (.var 1) (.succ (.var 0)))
      (.add (.mul (.var 1) (.var 0)) (.var 1)))))
  /-- The induction scheme. -/
  | induction (p : Formula) :
      PAaxiom (p.inst .zero ⟶ (.all (p ⟶ p.instSucc) ⟶ .all p))

/-- Derivability in `PA`: the Hilbert-style calculus with modus ponens and
generalization. -/
inductive Provable : Formula → Prop
  | ax {p : Formula} : PAaxiom p → Provable p
  | mp {p q : Formula} : Provable (p ⟶ q) → Provable p → Provable q
  | gen {p : Formula} : Provable p → Provable (.all p)

@[inherit_doc] notation:20 "PA" " ⊩ " p => Provable p

/-! ## Gödel numbering and the box modality -/

/-- Gödel numbering of terms. -/
def Term.encode : Term → ℕ
  | .var n => 5 * n + 1
  | .zero => 0
  | .succ t => 5 * t.encode + 2
  | .add t u => 5 * (Nat.pair t.encode u.encode) + 3
  | .mul t u => 5 * (Nat.pair t.encode u.encode) + 4

/-- Gödel numbering of formulas. -/
def Formula.encode : Formula → ℕ
  | .bot => 0
  | .eq t u => 4 * (Nat.pair t.encode u.encode) + 1
  | .imp p q => 4 * (Nat.pair p.encode q.encode) + 2
  | .all p => 4 * p.encode + 3

/-- The numeral `S^n 0` denoting the natural number `n`. -/
def numeral : ℕ → Term
  | 0 => .zero
  | n + 1 => .succ (numeral n)

/-- The closed term `⌜p⌝` denoting the Gödel number of the formula `p`. -/
def quote (p : Formula) : Term := numeral p.encode

/-- `box pr p` is the formula `pr(⌜p⌝)`, obtained by substituting the numeral of the
Gödel number of `p` for the free variable `0` of the formula `pr`. -/
def box (pr : Formula) (p : Formula) : Formula := pr.inst (quote p)

/-- A **provability predicate** for `PA`: a formula `pr` with one free variable
satisfying the three Hilbert–Bernays–Löb derivability conditions, together with the
diagonal (fixed point) lemma for the box modality it defines.  These are the standard
properties of the arithmetized provability predicate of `PA`. -/
structure ProvabilityPredicate where
  /-- The formula `Pr(x)` expressing provability, with one free variable `x`. -/
  pr : Formula
  /-- **D1** (necessitation): if `PA ⊩ p` then `PA ⊩ □p`. -/
  D1 : ∀ p : Formula, (PA ⊩ p) → (PA ⊩ box pr p)
  /-- **D2** (distribution): `PA ⊩ □(p → q) → (□p → □q)`. -/
  D2 : ∀ p q : Formula, PA ⊩ (box pr (p ⟶ q) ⟶ (box pr p ⟶ box pr q))
  /-- **D3**: `PA ⊩ □p → □□p`. -/
  D3 : ∀ p : Formula, PA ⊩ (box pr p ⟶ box pr (box pr p))
  /-- The **diagonal lemma** for the box modality: for every formula `p` there is a
  sentence `q` with `PA ⊩ q ↔ (□q → p)`. -/
  diagonal : ∀ p : Formula, ∃ q : Formula, PA ⊩ Formula.iff q (box pr q ⟶ p)

/-! ## Propositional reasoning inside `PA` -/

theorem provable_of_tautology {p : Formula} (h : Tautology p) : PA ⊩ p :=
  .ax (.taut h)

theorem mp_taut {p q : Formula} (h : Tautology (p ⟶ q)) (hp : PA ⊩ p) : PA ⊩ q :=
  .mp (provable_of_tautology h) hp

theorem iff_mp {p q : Formula} (h : PA ⊩ Formula.iff p q) : PA ⊩ (p ⟶ q) := by
  refine mp_taut (p := Formula.iff p q) ?_ h
  intro v
  simp only [Formula.iff, Formula.and, Formula.pEval]
  cases Formula.pEval v p <;> cases Formula.pEval v q <;> simp

theorem iff_mpr {p q : Formula} (h : PA ⊩ Formula.iff p q) : PA ⊩ (q ⟶ p) := by
  refine mp_taut (p := Formula.iff p q) ?_ h
  intro v
  simp only [Formula.iff, Formula.and, Formula.pEval]
  cases Formula.pEval v p <;> cases Formula.pEval v q <;> simp

/-- If `p` is provable, then so is `r ⟶ p` for any `r`. -/
theorem imp_of_provable {p : Formula} (r : Formula) (hp : PA ⊩ p) : PA ⊩ (r ⟶ p) := by
  refine mp_taut (p := p) ?_ hp
  intro v
  simp only [Formula.pEval]
  cases Formula.pEval v p <;> cases Formula.pEval v r <;> simp

/-- The propositional glue used in the proof of Löb's theorem. -/
theorem loeb_chain {a c d e f : Formula}
    (h1 : PA ⊩ (a ⟶ c)) (h2 : PA ⊩ (c ⟶ (d ⟶ e))) (h3 : PA ⊩ (a ⟶ d))
    (h4 : PA ⊩ (e ⟶ f)) : PA ⊩ (a ⟶ f) := by
  have key : Tautology ((a ⟶ c) ⟶ ((c ⟶ (d ⟶ e)) ⟶ ((a ⟶ d) ⟶ ((e ⟶ f) ⟶ (a ⟶ f))))) := by
    intro v
    simp only [Formula.pEval]
    cases Formula.pEval v a <;> cases Formula.pEval v c <;> cases Formula.pEval v d <;>
      cases Formula.pEval v e <;> cases Formula.pEval v f <;> simp
  exact .mp (.mp (.mp (.mp (provable_of_tautology key) h1) h2) h3) h4

/-! ## Löb's theorem -/

/-- **Löb's theorem**.  Let `Pr` be a provability predicate for Peano arithmetic, i.e. a
formula satisfying the Hilbert–Bernays–Löb derivability conditions and the diagonal
lemma, and write `□a` for `Pr(⌜a⌝)`.  If `PA ⊩ □a → a`, then `PA ⊩ a`. -/
theorem Loeb_theorem (P : ProvabilityPredicate) (a : Formula)
    (h : PA ⊩ (box P.pr a ⟶ a)) : PA ⊩ a := by
  obtain ⟨q, hq⟩ := P.diagonal a
  -- `PA ⊩ q → (□q → a)`
  have h1 : PA ⊩ (q ⟶ (box P.pr q ⟶ a)) := iff_mp hq
  -- `PA ⊩ □q → □(□q → a)`
  have h2 : PA ⊩ (box P.pr q ⟶ box P.pr (box P.pr q ⟶ a)) :=
    .mp (P.D2 q (box P.pr q ⟶ a)) (P.D1 _ h1)
  -- `PA ⊩ □(□q → a) → (□□q → □a)`
  have h3 : PA ⊩ (box P.pr (box P.pr q ⟶ a) ⟶ (box P.pr (box P.pr q) ⟶ box P.pr a)) :=
    P.D2 (box P.pr q) a
  -- `PA ⊩ □q → □□q`
  have h4 : PA ⊩ (box P.pr q ⟶ box P.pr (box P.pr q)) := P.D3 q
  -- `PA ⊩ □q → a`
  have h5 : PA ⊩ (box P.pr q ⟶ a) := loeb_chain h2 h3 h4 h
  -- hence `PA ⊩ q`, so `PA ⊩ □q`, so `PA ⊩ a`
  have h6 : PA ⊩ q := .mp (iff_mpr hq) h5
  exact .mp h5 (P.D1 _ h6)

/-! ## Non-vacuity of the hypotheses -/

/-- The trivial "provability predicate" `Pr(x) := (x = x)`, showing that the hypotheses
packaged in `ProvabilityPredicate` are consistent, so that `Loeb_theorem` is not
vacuously true. -/
theorem ProvabilityPredicate.nonempty : Nonempty ProvabilityPredicate := by
  have hb : ∀ p : Formula, PA ⊩ box (Formula.eq (.var 0) (.var 0)) p := by
    intro p
    exact .ax (.eqRefl _)
  refine ⟨{ pr := Formula.eq (.var 0) (.var 0), D1 := ?_, D2 := ?_, D3 := ?_,
            diagonal := ?_ }⟩
  · exact fun p _ => hb p
  · exact fun p q => imp_of_provable _ (imp_of_provable _ (hb q))
  · exact fun p => imp_of_provable _ (hb _)
  · refine fun p => ⟨p, ?_⟩
    refine mp_taut (p := box (Formula.eq (.var 0) (.var 0)) p) ?_ (hb p)
    intro v
    simp only [Formula.iff, Formula.and, Formula.pEval]
    cases Formula.pEval v (box (Formula.eq (Term.var 0) (Term.var 0)) p) <;>
      cases Formula.pEval v p <;> simp

/-- The Gödel numbering of terms is injective. -/
theorem Term.encode_injective : Function.Injective Term.encode := by
  intro t
  induction t with
  | var n =>
      intro u h; cases u <;> simp [Term.encode] at h ⊢ <;> omega
  | zero =>
      intro u h; cases u <;> simp [Term.encode] at h ⊢
  | succ t ih =>
      intro u h
      cases u <;> simp [Term.encode] at h ⊢ <;>
        first
          | omega
          | exact ih (by omega)
  | add t u iht ihu =>
      intro w h
      cases w <;> simp [Term.encode, Nat.pair_eq_pair] at h ⊢ <;>
        first
          | omega
          | exact ⟨iht h.1, ihu h.2⟩
  | mul t u iht ihu =>
      intro w h
      cases w <;> simp [Term.encode, Nat.pair_eq_pair] at h ⊢ <;>
        first
          | omega
          | exact ⟨iht h.1, ihu h.2⟩

/-- The Gödel numbering of formulas is injective. -/
theorem Formula.encode_injective : Function.Injective Formula.encode := by
  intro p
  induction p with
  | eq t u =>
      intro q h
      cases q <;> simp [Formula.encode, Nat.pair_eq_pair] at h ⊢ <;>
        first
          | omega
          | exact ⟨Term.encode_injective h.1, Term.encode_injective h.2⟩
  | bot =>
      intro q h
      cases q <;> simp [Formula.encode] at h ⊢
  | imp p q ihp ihq =>
      intro r h
      cases r <;> simp [Formula.encode, Nat.pair_eq_pair] at h ⊢ <;>
        first
          | omega
          | exact ⟨ihp h.1, ihq h.2⟩
  | all p ih =>
      intro q h
      cases q <;> simp [Formula.encode] at h ⊢ <;>
        first
          | omega
          | exact ih (by omega)

/-- Distinct formulas have distinct Gödel numerals, i.e. `⌜·⌝` is a genuine numbering. -/
theorem quote_injective : Function.Injective quote := by
  intro p q h
  refine Formula.encode_injective ?_
  have : ∀ m n : ℕ, numeral m = numeral n → m = n := by
    intro m
    induction m with
    | zero => intro n hn; cases n with
      | zero => rfl
      | succ n => simp [numeral] at hn
    | succ m ih => intro n hn; cases n with
      | zero => simp [numeral] at hn
      | succ n => simp only [numeral, Term.succ.injEq] at hn; exact congrArg _ (ih n hn)
  exact this _ _ h

/-! ## Standard semantics: soundness and consistency of `PA`

The following section checks that the proof calculus above is not degenerate: it is sound
for the standard model `ℕ`, and in particular `PA ⊬ ⊥`.
-/

/-- Extending an environment by a value for the de Bruijn variable `0`. -/
def cons (m : ℕ) (env : ℕ → ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => env n

/-- The value of a term in the standard model `ℕ`. -/
def Term.eval (env : ℕ → ℕ) : Term → ℕ
  | .var n => env n
  | .zero => 0
  | .succ t => t.eval env + 1
  | .add t u => t.eval env + u.eval env
  | .mul t u => t.eval env * u.eval env

/-- Truth of a formula in the standard model `ℕ`. -/
def Formula.holds : Formula → (ℕ → ℕ) → Prop
  | .eq t u, env => t.eval env = u.eval env
  | .bot, _ => False
  | .imp p q, env => p.holds env → q.holds env
  | .all p, env => ∀ m : ℕ, p.holds (cons m env)

theorem Term.eval_subst (σ : ℕ → Term) (env : ℕ → ℕ) (t : Term) :
    (t.subst σ).eval env = t.eval (fun n => (σ n).eval env) := by
  induction t <;> simp [Term.subst, Term.eval, *]

theorem Term.eval_shift (m : ℕ) (env : ℕ → ℕ) (t : Term) :
    t.shift.eval (cons m env) = t.eval env := by
  rw [Term.shift, Term.eval_subst]
  rfl

theorem Formula.holds_subst :
    ∀ (p : Formula) (σ : ℕ → Term) (env : ℕ → ℕ),
      (p.subst σ).holds env ↔ p.holds (fun n => (σ n).eval env)
  | .eq t u, σ, env => by simp [Formula.subst, Formula.holds, Term.eval_subst]
  | .bot, σ, env => Iff.rfl
  | .imp p q, σ, env => by
      simp [Formula.subst, Formula.holds, Formula.holds_subst p, Formula.holds_subst q]
  | .all p, σ, env => by
      simp only [Formula.subst, Formula.holds, Formula.holds_subst p]
      constructor
      · intro h m
        have := h m
        have he : (fun n => ((liftSubst σ) n).eval (cons m env))
            = cons m (fun n => (σ n).eval env) := by
          funext n
          cases n with
          | zero => rfl
          | succ n => exact Term.eval_shift m env (σ n)
        rwa [he] at this
      · intro h m
        have he : (fun n => ((liftSubst σ) n).eval (cons m env))
            = cons m (fun n => (σ n).eval env) := by
          funext n
          cases n with
          | zero => rfl
          | succ n => exact Term.eval_shift m env (σ n)
        rw [he]
        exact h m

theorem Formula.holds_inst (p : Formula) (t : Term) (env : ℕ → ℕ) :
    (p.inst t).holds env ↔ p.holds (cons (t.eval env) env) := by
  rw [Formula.inst, Formula.holds_subst]
  have : (fun n => (substOne t n).eval env) = cons (t.eval env) env := by
    funext n; cases n <;> rfl
  rw [this]

theorem Formula.holds_shift (p : Formula) (m : ℕ) (env : ℕ → ℕ) :
    p.shift.holds (cons m env) ↔ p.holds env := by
  rw [Formula.shift, Formula.holds_subst]
  have : (fun n => (Term.var (n + 1)).eval (cons m env)) = env := by
    funext n; rfl
  rw [this]

theorem Formula.holds_instSucc (p : Formula) (m : ℕ) (env : ℕ → ℕ) :
    p.instSucc.holds (cons m env) ↔ p.holds (cons (m + 1) env) := by
  rw [Formula.instSucc, Formula.holds_subst]
  have : (fun n => (match n with
      | 0 => Term.succ (Term.var 0)
      | (n + 1) => Term.var (n + 1)).eval (cons m env)) = cons (m + 1) env := by
    funext n; cases n <;> rfl
  rw [this]

/-- The truth-value assignment induced by the standard model. -/
noncomputable def truthVal (env : ℕ → ℕ) (p : Formula) : Bool :=
  @decide (p.holds env) (Classical.propDecidable _)

theorem truthVal_eq_true {env : ℕ → ℕ} {p : Formula} :
    truthVal env p = true ↔ p.holds env := by
  simp [truthVal]

theorem pEval_truthVal (env : ℕ → ℕ) :
    ∀ p : Formula, p.pEval (truthVal env) = truthVal env p
  | .eq _ _ => rfl
  | .all _ => rfl
  | .bot => by simp [Formula.pEval, truthVal, Formula.holds]
  | .imp p q => by
      simp only [Formula.pEval, pEval_truthVal env p, pEval_truthVal env q]
      by_cases hp : p.holds env <;> by_cases hq : q.holds env <;>
        simp [truthVal, Formula.holds, hp, hq]

/-- Every propositional tautology holds in the standard model. -/
theorem Tautology.holds {p : Formula} (h : Tautology p) (env : ℕ → ℕ) : p.holds env := by
  have := h (truthVal env)
  rw [pEval_truthVal env p] at this
  exact truthVal_eq_true.mp this

/-- Every axiom of `PA` holds in the standard model. -/
theorem PAaxiom.holds {p : Formula} (h : PAaxiom p) (env : ℕ → ℕ) : p.holds env := by
  induction h with
  | taut ht => exact ht.holds env
  | instantiate p t =>
      intro h
      rw [Formula.holds_inst]
      exact h _
  | allImp p q =>
      intro h hp m
      exact h m (hp m)
  | vacuous p =>
      intro h m
      exact (Formula.holds_shift p m env).mpr h
  | eqRefl t => rfl
  | eqSubst p t u =>
      intro he h
      rw [Formula.holds_inst] at h ⊢
      rwa [← he]
  | succNeZero => intro m h; simp [Formula.holds, Term.eval] at h
  | succInj => intro m k h; simpa [Formula.holds, Term.eval] using h
  | addZero => intro m; rfl
  | addSucc => intro m k; rfl
  | mulZero => intro m; simp [Formula.holds, Term.eval]
  | mulSucc =>
      intro m k
      simp only [Formula.holds, Term.eval, cons]
      ring
  | induction p =>
      intro h0 hstep m
      induction m with
      | zero => exact (Formula.holds_inst p .zero env).mp h0
      | succ n ih =>
          have := hstep n ih
          exact (Formula.holds_instSucc p n env).mp this

/-- **Soundness**: everything provable in `PA` holds in the standard model. -/
theorem Provable.sound {p : Formula} (h : Provable p) (env : ℕ → ℕ) : p.holds env := by
  induction h generalizing env with
  | ax ha => exact ha.holds env
  | mp _ _ ih1 ih2 => exact ih1 env (ih2 env)
  | gen _ ih => intro m; exact ih _

/-- **Consistency of `PA`**: `⊥` is not provable.  In particular the calculus above is
not degenerate, so Löb's theorem is not a triviality about an inconsistent theory. -/
theorem PA_consistent : ¬ (PA ⊩ Formula.bot) := fun h => h.sound (fun _ => 0)

end Frontier

