/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained: it uses no imports at all (only Lean 4 core),
so that the required header comment can literally be the first thing in the file
(Lean forbids `import` after a module docstring).

Contents:

* `Frontier.ATerm`, `Frontier.AFormula` : syntax of first-order arithmetic (de Bruijn variables).
* `Frontier.tval`, `Frontier.Sat`       : Tarskian semantics in the standard model `Nat`.
* `Frontier.enc`                        : a Gödel numbering of formulas.
* `Frontier.Defines`, `Frontier.Arithmetical` : arithmetical definability of a set of naturals.
* `Frontier.TrueSentences`              : arithmetical truth, i.e. the set of Gödel numbers of
                                          true sentences of arithmetic.
* `Frontier.Tarski_undefinability`      : arithmetical truth is not arithmetically definable.
* `Frontier.exists_subFree_equiv`       : the primitive substitution constructor of the syntax
                                          is eliminable, so the formulas above express exactly
                                          the conditions expressible in the ordinary language
                                          of arithmetic.
* `Frontier.Tarski_undefinability_subFree` : the same undefinability statement, restricted to
                                          formulas of that ordinary language.
-/

set_option autoImplicit false

namespace Frontier

/-! ## Syntax of the language of arithmetic

Variables are de Bruijn indices (natural numbers); an assignment is a function `Nat → Nat`. -/

/-- Terms of the language of arithmetic: variables, numerals, addition, multiplication. -/
inductive ATerm : Type
  | var : Nat → ATerm
  | num : Nat → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq

/-- Formulas of the language of arithmetic.

Besides the usual clauses (equations, negation, conjunction, existential quantification over
the variable with de Bruijn index `0`), the syntax has a primitive *substitution* constructor
`sub p t`, whose semantics (see `Sat`) is the usual semantics of the substituted formula
`p[t/x₀]`.  Making substitution a syntactic primitive rather than a defined operation on syntax
trees does not change which truth conditions are expressible, but it allows a Gödel numbering
for which substitution of a numeral acts on codes by an explicit polynomial; this is what
replaces the usual arithmetization of syntax. -/
inductive AFormula : Type
  | eq : ATerm → ATerm → AFormula
  | not : AFormula → AFormula
  | and : AFormula → AFormula → AFormula
  | ex : AFormula → AFormula
  | sub : AFormula → ATerm → AFormula
  deriving DecidableEq

/-- Extend an assignment by a value for the variable with de Bruijn index `0`. -/
def cons (n : Nat) (env : Nat → Nat) : Nat → Nat
  | 0 => n
  | (i + 1) => env i

/-- Value of a term under an assignment. -/
def tval (env : Nat → Nat) : ATerm → Nat
  | .var i => env i
  | .num n => n
  | .add a b => tval env a + tval env b
  | .mul a b => tval env a * tval env b

/-- Satisfaction of a formula in the standard model `Nat` under an assignment. -/
def Sat : (Nat → Nat) → AFormula → Prop
  | env, .eq a b => tval env a = tval env b
  | env, .not p => ¬ Sat env p
  | env, .and p q => Sat env p ∧ Sat env q
  | env, .ex p => ∃ n, Sat (cons n env) p
  | env, .sub p t => Sat (cons (tval env t) env) p

@[simp] theorem Sat_eq (env : Nat → Nat) (a b : ATerm) :
    Sat env (.eq a b) ↔ tval env a = tval env b := Iff.rfl

@[simp] theorem Sat_not (env : Nat → Nat) (p : AFormula) :
    Sat env (.not p) ↔ ¬ Sat env p := Iff.rfl

@[simp] theorem Sat_and (env : Nat → Nat) (p q : AFormula) :
    Sat env (.and p q) ↔ Sat env p ∧ Sat env q := Iff.rfl

@[simp] theorem Sat_ex (env : Nat → Nat) (p : AFormula) :
    Sat env (.ex p) ↔ ∃ n, Sat (cons n env) p := Iff.rfl

@[simp] theorem Sat_sub (env : Nat → Nat) (p : AFormula) (t : ATerm) :
    Sat env (.sub p t) ↔ Sat (cons (tval env t) env) p := Iff.rfl

/-! ## Gödel numbering

The numbering is chosen so that all coding operations are given by polynomials with natural
number coefficients, hence are themselves expressible by terms of the language. -/

/-- An injective polynomial pairing function on `Nat` (twice the Cantor pairing function). -/
def pairPoly (a b : Nat) : Nat := (a + b) * (a + b + 1) + 2 * a

private theorem pairPoly_aux {s t a c : Nat} (h : s < t) (ha : a ≤ s) :
    s * (s + 1) + 2 * a < t * (t + 1) + 2 * c := by
  have h1 : (s + 1) * (s + 2) ≤ t * (t + 1) := Nat.mul_le_mul h (by omega)
  have e1 : (s + 1) * (s + 2) = s * s + 3 * s + 2 := by
    simp [Nat.mul_add, Nat.add_mul]; omega
  have e2 : s * (s + 1) = s * s + s := by simp [Nat.mul_add]
  omega

theorem pairPoly_inj {a b c d : Nat} (h : pairPoly a b = pairPoly c d) : a = c ∧ b = d := by
  unfold pairPoly at h
  have hs : a + b = c + d := by
    rcases Nat.lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
    · exact absurd h (Nat.ne_of_lt (pairPoly_aux hlt (Nat.le_add_right a b)))
    · exact heq
    · exact absurd h.symm (Nat.ne_of_lt (pairPoly_aux hgt (Nat.le_add_right c d)))
  rw [hs] at h
  have h2 : 2 * a = 2 * c := Nat.add_left_cancel h
  exact ⟨by omega, by omega⟩

/-- Gödel numbering of terms. -/
def encT : ATerm → Nat
  | .var i => 4 * i
  | .num n => 4 * n + 1
  | .add a b => 4 * pairPoly (encT a) (encT b) + 2
  | .mul a b => 4 * pairPoly (encT a) (encT b) + 3

/-- Gödel numbering of formulas. -/
def enc : AFormula → Nat
  | .eq a b => 5 * pairPoly (encT a) (encT b)
  | .not p => 5 * enc p + 1
  | .and p q => 5 * pairPoly (enc p) (enc q) + 2
  | .ex p => 5 * enc p + 3
  | .sub p t => 5 * pairPoly (enc p) (encT t) + 4

theorem encT_injective : ∀ s t : ATerm, encT s = encT t → s = t := by
  intro s
  induction s with
  | var i =>
      intro t; cases t with
      | var j => intro h; simp only [encT] at h; exact congrArg ATerm.var (by omega)
      | num n => intro h; simp only [encT] at h; omega
      | add c d => intro h; simp only [encT] at h; omega
      | mul c d => intro h; simp only [encT] at h; omega
  | num n =>
      intro t; cases t with
      | var j => intro h; simp only [encT] at h; omega
      | num k => intro h; simp only [encT] at h; exact congrArg ATerm.num (by omega)
      | add c d => intro h; simp only [encT] at h; omega
      | mul c d => intro h; simp only [encT] at h; omega
  | add a b iha ihb =>
      intro t; cases t with
      | var j => intro h; simp only [encT] at h; omega
      | num k => intro h; simp only [encT] at h; omega
      | add c d =>
          intro h; simp only [encT] at h
          obtain ⟨h1, h2⟩ := pairPoly_inj (a := encT a) (b := encT b) (c := encT c) (d := encT d) (by omega)
          rw [iha c h1, ihb d h2]
      | mul c d => intro h; simp only [encT] at h; omega
  | mul a b iha ihb =>
      intro t; cases t with
      | var j => intro h; simp only [encT] at h; omega
      | num k => intro h; simp only [encT] at h; omega
      | add c d => intro h; simp only [encT] at h; omega
      | mul c d =>
          intro h; simp only [encT] at h
          obtain ⟨h1, h2⟩ := pairPoly_inj (a := encT a) (b := encT b) (c := encT c) (d := encT d) (by omega)
          rw [iha c h1, ihb d h2]

theorem enc_injective : ∀ p q : AFormula, enc p = enc q → p = q := by
  intro p
  induction p with
  | eq a b =>
      intro q; cases q with
      | eq c d =>
          intro h; simp only [enc] at h
          obtain ⟨h1, h2⟩ := pairPoly_inj (a := encT a) (b := encT b) (c := encT c) (d := encT d) (by omega)
          rw [encT_injective a c h1, encT_injective b d h2]
      | not r => intro h; simp only [enc] at h; omega
      | and r s => intro h; simp only [enc] at h; omega
      | ex r => intro h; simp only [enc] at h; omega
      | sub r t => intro h; simp only [enc] at h; omega
  | not r ih =>
      intro q; cases q with
      | eq c d => intro h; simp only [enc] at h; omega
      | not s => intro h; simp only [enc] at h; rw [ih s (by omega)]
      | and s u => intro h; simp only [enc] at h; omega
      | ex s => intro h; simp only [enc] at h; omega
      | sub s t => intro h; simp only [enc] at h; omega
  | and r s ihr ihs =>
      intro q; cases q with
      | eq c d => intro h; simp only [enc] at h; omega
      | not u => intro h; simp only [enc] at h; omega
      | and u v =>
          intro h; simp only [enc] at h
          obtain ⟨h1, h2⟩ := pairPoly_inj (a := enc r) (b := enc s) (c := enc u) (d := enc v) (by omega)
          rw [ihr u h1, ihs v h2]
      | ex u => intro h; simp only [enc] at h; omega
      | sub u t => intro h; simp only [enc] at h; omega
  | ex r ih =>
      intro q; cases q with
      | eq c d => intro h; simp only [enc] at h; omega
      | not s => intro h; simp only [enc] at h; omega
      | and s u => intro h; simp only [enc] at h; omega
      | ex s => intro h; simp only [enc] at h; rw [ih s (by omega)]
      | sub s t => intro h; simp only [enc] at h; omega
  | sub r t ih =>
      intro q; cases q with
      | eq c d => intro h; simp only [enc] at h; omega
      | not s => intro h; simp only [enc] at h; omega
      | and s u => intro h; simp only [enc] at h; omega
      | ex s => intro h; simp only [enc] at h; omega
      | sub s u =>
          intro h; simp only [enc] at h
          obtain ⟨h1, h2⟩ := pairPoly_inj (a := enc r) (b := encT t) (c := enc s) (d := encT u) (by omega)
          rw [ih s h1, encT_injective t u h2]

/-! ## Definability and arithmetical truth -/

/-- The formula `θ` *defines* the set `A` of naturals: the variable `x₀` is (semantically) the
only free variable of `θ`, and `θ` holds of `n` exactly when `n ∈ A`. -/
def Defines (θ : AFormula) (A : Nat → Prop) : Prop :=
  ∀ (env : Nat → Nat) (n : Nat), (Sat (cons n env) θ ↔ A n)

/-- A set of naturals is *arithmetical* if some formula of arithmetic defines it. -/
def Arithmetical (A : Nat → Prop) : Prop := ∃ θ : AFormula, Defines θ A

/-- A formula is a *sentence* if its truth value does not depend on the assignment. -/
def IsSentence (p : AFormula) : Prop := ∀ env env' : Nat → Nat, Sat env p ↔ Sat env' p

/-- *Arithmetical truth*: the set of Gödel numbers of true sentences of arithmetic. -/
def TrueSentences (n : Nat) : Prop :=
  ∃ p : AFormula, IsSentence p ∧ enc p = n ∧ Sat (fun _ => 0) p

theorem mem_TrueSentences_iff {p : AFormula} (hp : IsSentence p) :
    TrueSentences (enc p) ↔ Sat (fun _ => 0) p := by
  constructor
  · intro h
    obtain ⟨q, _, hqe, hqs⟩ := h
    rwa [enc_injective q p hqe] at hqs
  · intro h
    exact ⟨p, hp, rfl, h⟩

/-! ## Tarski's undefinability theorem -/

/-- The term computing, from the value `m` of the variable `x₀`, the number
`5 * pairPoly m (4 * m + 1) + 4`; if `m` is the Gödel number of a formula `p`, this is the
Gödel number of the instance `AFormula.sub p (num m)` of `p` at its own code. -/
def diagTerm : ATerm :=
  .add
    (.mul (.num 5)
      (.add
        (.mul (.add (.var 0) (.add (.mul (.num 4) (.var 0)) (.num 1)))
              (.add (.add (.var 0) (.add (.mul (.num 4) (.var 0)) (.num 1))) (.num 1)))
        (.mul (.num 2) (.var 0))))
    (.num 4)

theorem tval_diagTerm (env : Nat → Nat) (m : Nat) :
    tval (cons m env) diagTerm = 5 * pairPoly m (4 * m + 1) + 4 := rfl

/-- Given `θ`, the formula `¬ θ(diagTerm(x₀))` with free variable `x₀`. -/
def diagFormula (θ : AFormula) : AFormula := .not (.sub θ diagTerm)

/-- The Tarski diagonal sentence for `θ`: `diagFormula θ` applied to its own Gödel number. -/
def diagSentence (θ : AFormula) : AFormula :=
  .sub (diagFormula θ) (.num (enc (diagFormula θ)))

theorem enc_diagSentence (θ : AFormula) :
    enc (diagSentence θ) = 5 * pairPoly (enc (diagFormula θ)) (4 * enc (diagFormula θ) + 1) + 4 :=
  rfl

/-- The fixed point property of the diagonal sentence: it asserts its own untruth, relative to
a formula `θ` defining arithmetical truth. -/
theorem diagSentence_iff {θ : AFormula} (hθ : Defines θ TrueSentences) (env : Nat → Nat) :
    Sat env (diagSentence θ) ↔ ¬ TrueSentences (enc (diagSentence θ)) := by
  have h1 : Sat env (diagSentence θ) ↔
      ¬ Sat (cons (tval (cons (enc (diagFormula θ)) env) diagTerm)
          (cons (enc (diagFormula θ)) env)) θ := Iff.rfl
  rw [h1, tval_diagTerm, ← enc_diagSentence θ,
    hθ (cons (enc (diagFormula θ)) env) (enc (diagSentence θ))]

/-- **Tarski's undefinability theorem.** Arithmetical truth — the set of Gödel numbers of true
sentences of first-order arithmetic — is not arithmetically definable. -/
theorem Tarski_undefinability : ¬ Arithmetical TrueSentences := by
  intro hA
  obtain ⟨θ, hθ⟩ := hA
  have key := diagSentence_iff hθ
  have hsent : IsSentence (diagSentence θ) := fun env env' => (key env).trans (key env').symm
  have htrue := mem_TrueSentences_iff hsent
  have hn : ¬ Sat (fun _ => 0) (diagSentence θ) :=
    fun hs => (key (fun _ => 0)).mp hs (htrue.mpr hs)
  exact hn ((key (fun _ => 0)).mpr (fun hT => hn (htrue.mp hT)))

/-! ## Sanity checks

These confirm that the notions above are not vacuous: some sets are arithmetical, and
`TrueSentences` is a nontrivial set of naturals. -/

/-- The formula `∃ x₁, x₀ = 2 * x₁` (de Bruijn: under the quantifier, `x₀` becomes `x₁`). -/
def evenFormula : AFormula := .ex (.eq (.var 1) (.mul (.num 2) (.var 0)))

/-- The set of even numbers is arithmetical. -/
theorem arithmetical_even : Arithmetical (fun n => ∃ k, n = 2 * k) :=
  ⟨evenFormula, fun _ _ => Iff.rfl⟩

/-- The sentence `0 = 0`. -/
def trivSentence : AFormula := .eq (.num 0) (.num 0)

theorem isSentence_trivSentence : IsSentence trivSentence := fun _ _ => Iff.rfl

theorem isSentence_not_trivSentence : IsSentence (.not trivSentence) := fun _ _ => Iff.rfl

/-- `0 = 0` is a true sentence, so its code lies in `TrueSentences`. -/
theorem trivSentence_mem : TrueSentences (enc trivSentence) :=
  ⟨trivSentence, isSentence_trivSentence, rfl, rfl⟩

/-- `¬ (0 = 0)` is a false sentence, so its code does not lie in `TrueSentences`. -/
theorem not_trivSentence_not_mem : ¬ TrueSentences (enc (.not trivSentence)) := by
  intro h
  exact (mem_TrueSentences_iff isSentence_not_trivSentence).mp h rfl

/-! ## The substitution constructor is eliminable

The syntax `AFormula` has a primitive substitution constructor `sub`.  We show that it adds no
expressive power: every formula is logically equivalent (in the standard model, under every
assignment) to one in the ordinary language of arithmetic, built only from equations,
negation, conjunction and existential quantification. -/

/-- A formula is `SubFree` if it does not use the primitive substitution constructor. -/
def SubFree : AFormula → Prop
  | .eq _ _ => True
  | .not p => SubFree p
  | .and p q => SubFree p ∧ SubFree q
  | .ex p => SubFree p
  | .sub _ _ => False

/-- Shift all de Bruijn indices of a term up by `n`. -/
def shiftT (n : Nat) : ATerm → ATerm
  | .var i => .var (i + n)
  | .num k => .num k
  | .add a b => .add (shiftT n a) (shiftT n b)
  | .mul a b => .mul (shiftT n a) (shiftT n b)

/-- Substitute the term `t` for the variable `xₙ` in a term, decreasing the indices of the
variables above `n` (so that `n` binders have been passed). -/
def tsub (n : Nat) (t : ATerm) : ATerm → ATerm
  | .var i => if i < n then .var i else if i = n then shiftT n t else .var (i - 1)
  | .num k => .num k
  | .add a b => .add (tsub n t a) (tsub n t b)
  | .mul a b => .mul (tsub n t a) (tsub n t b)

/-- Substitute the term `t` for the variable `xₙ` in a formula. -/
def fsub (t : ATerm) : Nat → AFormula → AFormula
  | n, .eq a b => .eq (tsub n t a) (tsub n t b)
  | n, .not p => .not (fsub t n p)
  | n, .and p q => .and (fsub t n p) (fsub t n q)
  | n, .ex p => .ex (fsub t (n + 1) p)
  | n, .sub p u => .sub (fsub t n p) (tsub n t u)

/-- Rewrite a formula into an equivalent one without the primitive substitution constructor. -/
def elim : AFormula → AFormula
  | .eq a b => .eq a b
  | .not p => .not (elim p)
  | .and p q => .and (elim p) (elim q)
  | .ex p => .ex (elim p)
  | .sub p t => fsub t 0 (elim p)

/-- Insert the value `v` at position `n` in an assignment. -/
def insertEnv (n v : Nat) (env : Nat → Nat) : Nat → Nat :=
  fun i => if i < n then env i else if i = n then v else env (i - 1)

theorem tval_shiftT (env : Nat → Nat) (n : Nat) :
    ∀ t : ATerm, tval env (shiftT n t) = tval (fun i => env (i + n)) t := by
  intro t
  induction t with
  | var i => rfl
  | num k => rfl
  | add a b iha ihb => simp only [shiftT, tval, iha, ihb]
  | mul a b iha ihb => simp only [shiftT, tval, iha, ihb]

theorem tval_tsub (t : ATerm) (n : Nat) (env : Nat → Nat) :
    ∀ s : ATerm,
      tval env (tsub n t s) = tval (insertEnv n (tval (fun i => env (i + n)) t) env) s := by
  intro s
  induction s with
  | var i =>
      by_cases h1 : i < n
      · simp [tsub, insertEnv, h1, tval]
      · by_cases h2 : i = n
        · simp [tsub, insertEnv, h2, tval, tval_shiftT]
        · simp [tsub, insertEnv, h1, h2, tval]
  | num k => rfl
  | add a b iha ihb => simp only [tsub, tval, iha, ihb]
  | mul a b iha ihb => simp only [tsub, tval, iha, ihb]

theorem insertEnv_cons (n v k : Nat) (env : Nat → Nat) :
    insertEnv (n + 1) v (cons k env) = cons k (insertEnv n v env) := by
  funext i
  cases i with
  | zero => simp [insertEnv, cons]
  | succ j =>
      by_cases h1 : j < n
      · simp [insertEnv, cons, h1, Nat.succ_lt_succ_iff]
      · by_cases h2 : j = n
        · simp [insertEnv, cons, h2]
        · have hj : 1 ≤ j := by omega
          have : j + 1 - 1 = (j - 1) + 1 := by omega
          simp only [insertEnv, cons, Nat.succ_lt_succ_iff, if_neg h1,
            if_neg (show j + 1 ≠ n + 1 by omega), this]
          cases j with
          | zero => omega
          | succ j' => simp [if_neg h2]

theorem insertEnv_zero (v : Nat) (env : Nat → Nat) : insertEnv 0 v env = cons v env := by
  funext i
  cases i with
  | zero => simp [insertEnv, cons]
  | succ j => simp [insertEnv, cons]

theorem Sat_fsub (t : ATerm) :
    ∀ (q : AFormula), SubFree q → ∀ (n : Nat) (env : Nat → Nat),
      (Sat env (fsub t n q) ↔ Sat (insertEnv n (tval (fun i => env (i + n)) t) env) q) := by
  intro q
  induction q with
  | eq a b => intro _ n env; simp only [fsub, Sat_eq, tval_tsub]
  | not p ih => intro hq n env; simp only [fsub, Sat_not, ih hq n env]
  | and p r ihp ihr =>
      intro hq n env
      simp only [fsub, Sat_and, ihp hq.1 n env, ihr hq.2 n env]
  | ex p ih =>
      intro hq n env
      simp only [fsub, Sat_ex, ih hq (n + 1)]
      constructor
      · intro h
        obtain ⟨k, hk⟩ := h
        exact ⟨k, by rw [insertEnv_cons] at hk; exact hk⟩
      · intro h
        obtain ⟨k, hk⟩ := h
        exact ⟨k, by rw [insertEnv_cons]; exact hk⟩
  | sub p u _ => intro hq; exact absurd hq (fun h => h)

theorem SubFree_fsub (t : ATerm) :
    ∀ (q : AFormula), SubFree q → ∀ n : Nat, SubFree (fsub t n q) := by
  intro q
  induction q with
  | eq a b => intro _ _; trivial
  | not p ih => intro hq n; exact ih hq n
  | and p r ihp ihr => intro hq n; exact ⟨ihp hq.1 n, ihr hq.2 n⟩
  | ex p ih => intro hq n; exact ih hq (n + 1)
  | sub p u _ => intro hq; exact absurd hq (fun h => h)

theorem SubFree_elim : ∀ p : AFormula, SubFree (elim p) := by
  intro p
  induction p with
  | eq a b => trivial
  | not p ih => exact ih
  | and p q ihp ihq => exact ⟨ihp, ihq⟩
  | ex p ih => exact ih
  | sub p t ih => exact SubFree_fsub t (elim p) ih 0

theorem Sat_elim : ∀ (p : AFormula) (env : Nat → Nat), Sat env (elim p) ↔ Sat env p := by
  intro p
  induction p with
  | eq a b => intro env; exact Iff.rfl
  | not p ih => intro env; simp only [elim, Sat_not, ih env]
  | and p q ihp ihq => intro env; simp only [elim, Sat_and, ihp env, ihq env]
  | ex p ih => intro env; simp only [elim, Sat_ex, ih]
  | sub p t ih =>
      intro env
      have h := Sat_fsub t (elim p) (SubFree_elim p) 0 env
      simp only [Nat.add_zero] at h
      simp only [elim, Sat_sub]
      rw [h, insertEnv_zero, ih (cons (tval env t) env)]

/-- Every formula is equivalent, under every assignment, to a formula of the ordinary language
of arithmetic (no primitive substitution constructor). -/
theorem exists_subFree_equiv (p : AFormula) :
    ∃ q : AFormula, SubFree q ∧ ∀ env : Nat → Nat, (Sat env q ↔ Sat env p) :=
  ⟨elim p, SubFree_elim p, Sat_elim p⟩

/-- **Tarski's undefinability theorem, for the ordinary language of arithmetic.**  Arithmetical
truth is not defined by any formula built from equations, negation, conjunction and existential
quantification. -/
theorem Tarski_undefinability_subFree :
    ¬ ∃ θ : AFormula, SubFree θ ∧ Defines θ TrueSentences := by
  intro h
  obtain ⟨θ, _, hθ⟩ := h
  exact Tarski_undefinability ⟨θ, hθ⟩

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

