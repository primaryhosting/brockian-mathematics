/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Hilbert's tenth problem asks for an algorithm which decides whether a polynomial equation
with integer coefficients has a solution in natural numbers.  We formalise instances of
the problem as pairs `(P, Q)` of polynomials with *natural* coefficients (an equation with
integer coefficients is turned into this shape by moving negative monomials to the other
side), encoded concretely as lists of monomials, so that instances form a `Primcodable`
type and "algorithm" can be taken to mean `Computable` in Mathlib's sense.

The main theorem `CS.hilbert10_undecidable` states that, granted the MRDP theorem — every
computably enumerable predicate on `ℕ` is Diophantine, phrased with Mathlib's own `Dioph`
predicate — solvability of such equations is not a computable predicate.  MRDP itself is
not available in Mathlib and is not proved here; it enters as an explicit hypothesis
`CS.Hilbert10.MRDP` of the main theorem (no axiom is added to the environment).

Everything else is proved unconditionally:

* `CS.Hilbert10.dioph_to_eqn` and `CS.Hilbert10.eqn_to_dioph`: Mathlib's `Dioph` predicate
  for sets of naturals matches parametric solvability of a concrete equation of the above
  shape; `CS.Hilbert10.mrdp_iff` records the resulting reformulation of MRDP.
* `CS.Hilbert10.solvable_re`: solvability is computably enumerable (the easy half of
  MRDP: one can search for a solution).
* `CS.Hilbert10.specialize` and `CS.Hilbert10.computable_specialize`: substituting a value
  for the parameter `x 0` is a primitive recursive operation on equations, and
  `CS.Hilbert10.solvable_specialize` shows it does what it should.
* `CS.Hilbert10.undecidable_of_dioph`: *any* undecidable Diophantine predicate on `ℕ`
  makes Hilbert's tenth problem undecidable; the main theorem instantiates this with the
  halting problem, so only Diophantineness of the halting set is actually used.
-/

namespace CS

namespace Hilbert10

/-- A monomial in variables indexed by `γ`: a natural number coefficient together with the
list of variable indices occurring in it (with multiplicity).  The monomial `(c, [i, j, i])`
denotes `c * x i * x j * x i`. -/
abbrev Mon (γ : Type*) := ℕ × List γ

/-- A polynomial with natural number coefficients in variables indexed by `γ`, represented
as a list of monomials (to be summed). -/
abbrev NPoly (γ : Type*) := List (Mon γ)

/-- An instance of Hilbert's tenth problem: a Diophantine equation `P = Q`, given by a pair
of polynomials with natural coefficients in the variables `x 0, x 1, …`.  Every polynomial
equation with integer coefficients can be put in this form by moving the negative monomials
to the other side. -/
abbrev Eqn := NPoly ℕ × NPoly ℕ

variable {γ δ : Type*}

/-- Value of a monomial at an assignment of natural numbers to the variables. -/
def evalMon (m : Mon γ) (v : γ → ℕ) : ℕ := m.1 * (m.2.map v).prod

/-- Value of a polynomial at an assignment of natural numbers to the variables. -/
def eval (p : NPoly γ) (v : γ → ℕ) : ℕ := (p.map fun m => evalMon m v).sum

/-- Hilbert's tenth problem: does the equation `P = Q` have a solution in natural numbers? -/
def Solvable (e : Eqn) : Prop := ∃ v : ℕ → ℕ, eval e.1 v = eval e.2 v

/-- Sum of two polynomials. -/
def padd (p q : NPoly γ) : NPoly γ := p ++ q

/-- Product of two polynomials. -/
def pmul (p q : NPoly γ) : NPoly γ :=
  p.flatMap fun m => q.map fun m' => (m.1 * m'.1, m.2 ++ m'.2)

/-- The constant polynomial. -/
def pconst (c : ℕ) : NPoly γ := [(c, [])]

/-- The polynomial consisting of a single variable. -/
def pvar (i : γ) : NPoly γ := [(1, [i])]

/-- Renaming the variables of a polynomial along `r`. -/
def prename (r : γ → δ) (p : NPoly γ) : NPoly δ := p.map fun m => (m.1, m.2.map r)

/-- The list of variables occurring in a polynomial. -/
def vars (p : NPoly γ) : List γ := p.flatMap fun m => m.2

@[simp] lemma eval_nil (v : γ → ℕ) : eval ([] : NPoly γ) v = 0 := rfl

@[simp] lemma eval_cons (m : Mon γ) (p : NPoly γ) (v : γ → ℕ) :
    eval (m :: p) v = evalMon m v + eval p v := rfl

@[simp] lemma eval_append (p q : NPoly γ) (v : γ → ℕ) :
    eval (p ++ q) v = eval p v + eval q v := by
  simp [eval]

@[simp] lemma eval_padd (p q : NPoly γ) (v : γ → ℕ) :
    eval (padd p q) v = eval p v + eval q v := by
  simp [padd]

@[simp] lemma eval_pconst (c : ℕ) (v : γ → ℕ) : eval (pconst c) v = c := by
  simp [pconst, eval, evalMon]

@[simp] lemma eval_pvar (i : γ) (v : γ → ℕ) : eval (pvar i) v = v i := by
  simp [pvar, eval, evalMon]

lemma eval_mapMul (m : Mon γ) (q : NPoly γ) (v : γ → ℕ) :
    eval (q.map fun m' => (m.1 * m'.1, m.2 ++ m'.2)) v = evalMon m v * eval q v := by
  induction q with
  | nil => simp [eval]
  | cons m' q ih =>
      simp only [List.map_cons, eval_cons, ih, evalMon, List.map_append, List.prod_append]
      ring

@[simp] lemma eval_pmul (p q : NPoly γ) (v : γ → ℕ) :
    eval (pmul p q) v = eval p v * eval q v := by
  induction p with
  | nil => simp [pmul, eval]
  | cons m p ih =>
      have h : pmul (m :: p) q = (q.map fun m' => (m.1 * m'.1, m.2 ++ m'.2)) ++ pmul p q := by
        simp [pmul]
      rw [h, eval_append, eval_mapMul, ih, eval_cons]
      ring

@[simp] lemma eval_prename (r : γ → δ) (p : NPoly γ) (w : δ → ℕ) :
    eval (prename r p) w = eval p (w ∘ r) := by
  induction p with
  | nil => simp [prename, eval]
  | cons m p ih =>
      simp only [prename, List.map_cons, eval_cons, evalMon, List.map_map] at *
      rw [ih]

lemma eval_congr {p : NPoly γ} {x y : γ → ℕ} (h : ∀ j ∈ vars p, x j = y j) :
    eval p x = eval p y := by
  induction p with
  | nil => rfl
  | cons m p ih =>
      have hm : ∀ j ∈ m.2, x j = y j := fun j hj => h j (by simp [vars, hj])
      have hp : ∀ j ∈ vars p, x j = y j := fun j hj => by
        refine h j ?_
        simp only [vars, List.flatMap_cons, List.mem_append]
        exact Or.inr hj
      have : (m.2.map x) = (m.2.map y) := List.map_congr_left hm
      simp only [eval_cons, evalMon, this, ih hp]

/-- Every multivariate integer polynomial in Mathlib's sense is the difference of two
polynomials with natural coefficients. -/
lemma isPoly_repr {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ P Q : NPoly γ, ∀ x, f x = (eval P x : ℤ) - (eval Q x : ℤ) := by
  induction hf with
  | proj i => exact ⟨pvar i, [], by intro x; simp⟩
  | const n =>
      refine ⟨pconst n.toNat, pconst (-n).toNat, fun x => ?_⟩
      simp only [eval_pconst]
      omega
  | @sub f g _ _ ihf ihg =>
      obtain ⟨P₁, Q₁, h₁⟩ := ihf
      obtain ⟨P₂, Q₂, h₂⟩ := ihg
      refine ⟨padd P₁ Q₂, padd Q₁ P₂, fun x => ?_⟩
      simp only [eval_padd, h₁, h₂, Nat.cast_add]
      ring
  | @mul f g _ _ ihf ihg =>
      obtain ⟨P₁, Q₁, h₁⟩ := ihf
      obtain ⟨P₂, Q₂, h₂⟩ := ihg
      refine ⟨padd (pmul P₁ P₂) (pmul Q₁ Q₂), padd (pmul P₁ Q₂) (pmul Q₁ P₂), fun x => ?_⟩
      simp only [eval_padd, eval_pmul, h₁, h₂, Nat.cast_add, Nat.cast_mul]
      ring

/-- Translation from Mathlib's `Dioph` predicate to concrete equations: if the set of
naturals `S` is Diophantine, then there is an equation `P = Q` in the variables
`x 0, x 1, …` such that `n ∈ S` exactly when the equation has a solution with `x 0 = n`. -/
lemma dioph_to_eqn {S : ℕ → Prop} (h : Dioph {v : Unit → ℕ | S (v ())}) :
    ∃ e : Eqn, ∀ n : ℕ, S n ↔ ∃ w : ℕ → ℕ, w 0 = n ∧ eval e.1 w = eval e.2 w := by
  obtain ⟨β, p, hp⟩ := h
  letI : DecidableEq (Unit ⊕ β) := Classical.decEq _
  obtain ⟨P, Q, hPQ⟩ := isPoly_repr p.isPoly
  set L : List (Unit ⊕ β) := vars P ++ vars Q with hL
  set ren : Unit ⊕ β → ℕ := fun j => Sum.elim (fun _ => 0) (fun b => L.idxOf (Sum.inr b) + 1) j
    with hren
  set inv : ℕ → Unit ⊕ β := fun i => if i = 0 then Sum.inl () else L.getD (i - 1) (Sum.inl ())
    with hinv
  have hinv_ren : ∀ j ∈ L, inv (ren j) = j := by
    rintro (⟨⟩ | b) hj
    · simp [hinv, hren]
    · have hmem : Sum.inr b ∈ L := hj
      have hlt : L.idxOf (Sum.inr b) < L.length := List.idxOf_lt_length_of_mem hmem
      simp only [hinv, hren, Sum.elim_inr, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _)]
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf]
  refine ⟨(prename ren P, prename ren Q), fun n => ?_⟩
  have hpn : S n ↔ ∃ t, p (Sum.elim (fun _ => n) t) = 0 := hp (fun _ => n)
  rw [hpn]
  constructor
  · rintro ⟨t, ht⟩
    set x : Unit ⊕ β → ℕ := Sum.elim (fun _ => n) t with hx
    refine ⟨fun i => x (inv i), by simp [hx, hinv], ?_⟩
    have hPx : eval (prename ren P) (fun i => x (inv i)) = eval P x := by
      rw [eval_prename]
      refine eval_congr fun j hj => ?_
      have : j ∈ L := by simp only [hL, List.mem_append]; exact Or.inl hj
      simp only [Function.comp_apply, hinv_ren j this]
    have hQx : eval (prename ren Q) (fun i => x (inv i)) = eval Q x := by
      rw [eval_prename]
      refine eval_congr fun j hj => ?_
      have : j ∈ L := by simp only [hL, List.mem_append]; exact Or.inr hj
      simp only [Function.comp_apply, hinv_ren j this]
    rw [hPx, hQx]
    have := hPQ x
    rw [ht] at this
    have : (eval P x : ℤ) = (eval Q x : ℤ) := by linarith
    exact_mod_cast this
  · rintro ⟨w, hw0, hw⟩
    refine ⟨fun b => w (ren (Sum.inr b)), ?_⟩
    have hxw : Sum.elim (fun _ : Unit => n) (fun b => w (ren (Sum.inr b)))
        = fun j => w (ren j) := by
      funext j
      rcases j with ⟨⟩ | b
      · simp [hren, hw0]
      · simp
    rw [hPQ]
    rw [hxw]
    have hP := (eval_prename ren P w).symm
    have hQ := (eval_prename ren Q w).symm
    simp only [Function.comp_def] at hP hQ
    rw [hP, hQ, hw]
    ring

/-- The Mathlib polynomial (with integer coefficients) determined by a monomial. -/
def monToPoly (c : ℕ) : List γ → Poly γ
  | [] => Poly.const (c : ℤ)
  | i :: xs => Poly.proj i * monToPoly c xs

/-- The Mathlib polynomial (with integer coefficients) determined by a polynomial with
natural coefficients. -/
def toPoly : NPoly γ → Poly γ
  | [] => 0
  | m :: p => monToPoly m.1 m.2 + toPoly p

lemma monToPoly_apply (c : ℕ) (xs : List γ) (x : γ → ℕ) :
    monToPoly c xs x = (c : ℤ) * ((xs.map x).prod : ℕ) := by
  induction xs with
  | nil => simp [monToPoly]
  | cons i xs ih => simp [monToPoly, ih]; ring

lemma toPoly_apply (p : NPoly γ) (x : γ → ℕ) : toPoly p x = (eval p x : ℤ) := by
  induction p with
  | nil => simp [toPoly, eval]
  | cons m p ih => simp [toPoly, eval_cons, evalMon, monToPoly_apply, ih]

/-- Renaming used to view an equation in the variables `x 0, x 1, …` as an equation whose
variable `x 0` is a parameter and whose remaining variables are existentially quantified. -/
def paramRen : ℕ → Unit ⊕ ℕ := fun i => if i = 0 then Sum.inl () else Sum.inr i

/-- Converse of `dioph_to_eqn`: the parametric solvability of a concrete equation is a
Diophantine predicate in Mathlib's sense. -/
theorem eqn_to_dioph (e : Eqn) :
    Dioph {v : Unit → ℕ | ∃ w : ℕ → ℕ, w 0 = v () ∧ eval e.1 w = eval e.2 w} := by
  refine ⟨ℕ, toPoly (prename paramRen e.1) - toPoly (prename paramRen e.2), fun v => ?_⟩
  have key : ∀ t : ℕ → ℕ,
      (toPoly (prename paramRen e.1) - toPoly (prename paramRen e.2)) (Sum.elim v t) = 0 ↔
        eval e.1 (fun i => Sum.elim v t (paramRen i))
          = eval e.2 (fun i => Sum.elim v t (paramRen i)) := by
    intro t
    rw [Poly.sub_apply, toPoly_apply, toPoly_apply, eval_prename, eval_prename]
    constructor
    · intro h
      have : ((eval e.1 (fun i => Sum.elim v t (paramRen i)) : ℤ))
          = (eval e.2 (fun i => Sum.elim v t (paramRen i)) : ℤ) := by
        simp only [Function.comp_def] at h ⊢
        linarith
      exact_mod_cast this
    · intro h
      simp only [Function.comp_def, h]
      ring
  constructor
  · rintro ⟨w, hw0, hw⟩
    refine ⟨w, (key w).mpr ?_⟩
    have hxw : (fun i => Sum.elim v w (paramRen i)) = w := by
      funext i
      by_cases hi : i = 0
      · simp [paramRen, hi, hw0]
      · simp [paramRen, hi]
    rw [hxw]
    exact hw
  · rintro ⟨t, ht⟩
    refine ⟨fun i => Sum.elim v t (paramRen i), by simp [paramRen], (key t).mp ht⟩

/-- The **MRDP theorem** (Matiyasevich–Robinson–Davis–Putnam), stated with Mathlib's
`Dioph` predicate: every computably enumerable predicate on `ℕ` is Diophantine.  This deep
theorem is the input to the undecidability of Hilbert's tenth problem; it is taken here as
a hypothesis. -/
def MRDP : Prop :=
  ∀ S : ℕ → Prop, REPred S → Dioph {v : Unit → ℕ | S (v ())}

/-- MRDP is equivalent to the concrete statement that every computably enumerable
predicate on `ℕ` is the parametric solvability predicate of an explicit equation `P = Q`
with `x 0` as parameter. -/
theorem mrdp_iff : MRDP ↔ ∀ S : ℕ → Prop, REPred S →
    ∃ e : Eqn, ∀ n : ℕ, S n ↔ ∃ w : ℕ → ℕ, w 0 = n ∧ eval e.1 w = eval e.2 w := by
  constructor
  · intro h S hS
    exact dioph_to_eqn (h S hS)
  · intro h S hS
    obtain ⟨e, he⟩ := h S hS
    exact Dioph.ext (eqn_to_dioph e) fun v => (he (v ())).symm

/-- Fixed part of the left-hand side of the specialised equation. -/
def lhsFixed (e : Eqn) : NPoly ℕ :=
  padd (padd (pmul e.1 e.1) (pmul e.2 e.2)) (pmul (pvar 0) (pvar 0))

/-- Fixed part of the right-hand side of the specialised equation. -/
def rhsFixed (e : Eqn) : NPoly ℕ := pmul (pconst 2) (pmul e.1 e.2)

/-- Given a parametric equation `e` (with parameter `x 0`) and a value `n` for the
parameter, `specialize e n` is an equation which is solvable exactly when `e` has a
solution with `x 0 = n`.  Concretely it is `(P - Q) ^ 2 + (x 0 - n) ^ 2 = 0`, written with
natural coefficients only. -/
def specialize (e : Eqn) (n : ℕ) : Eqn :=
  (padd (lhsFixed e) (pconst (n * n)),
   padd (rhsFixed e) (pmul (pconst (2 * n)) (pvar 0)))

lemma specialize_eq (e : Eqn) (n : ℕ) :
    specialize e n = (lhsFixed e ++ [(n * n, ([] : List ℕ))],
      rhsFixed e ++ [(2 * n, [0])]) := by
  simp [specialize, padd, pconst, pvar, pmul]

/-- The natural-number identity encoding `(a - b) ^ 2 + (x - n) ^ 2 = 0`. -/
lemma sum_sq_eq_iff (a b x n : ℕ) :
    a * a + b * b + x * x + n * n = 2 * (a * b) + 2 * n * x ↔ a = b ∧ x = n := by
  constructor
  · intro h
    have h' : (a : ℤ) * a + b * b + x * x + n * n = 2 * (a * b) + 2 * n * x := by exact_mod_cast h
    have h1 : ((a : ℤ) - b) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((a : ℤ) - b), sq_nonneg ((x : ℤ) - n)]
    have h2 : ((x : ℤ) - n) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((a : ℤ) - b), sq_nonneg ((x : ℤ) - n)]
    have h1' : (a : ℤ) = b := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith
    have h2' : (x : ℤ) = n := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      linarith
    exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
  · rintro ⟨rfl, rfl⟩
    ring

lemma solvable_specialize (e : Eqn) (n : ℕ) :
    Solvable (specialize e n) ↔ ∃ v : ℕ → ℕ, v 0 = n ∧ eval e.1 v = eval e.2 v := by
  simp only [Solvable, specialize, lhsFixed, rhsFixed, eval_padd, eval_pmul, eval_pconst,
    eval_pvar]
  refine exists_congr fun v => ?_
  rw [sum_sq_eq_iff]
  tauto

lemma computable_specialize (e : Eqn) : Computable (specialize e) := by
  have h : Primrec fun n : ℕ => ((lhsFixed e ++ [(n * n, ([] : List ℕ))] : NPoly ℕ),
      (rhsFixed e ++ [(2 * n, [0])] : NPoly ℕ)) := by
    refine Primrec.pair ?_ ?_
    · refine Primrec₂.comp Primrec.list_append (Primrec.const _) ?_
      refine Primrec₂.comp Primrec.list_cons ?_ (Primrec.const [])
      exact Primrec.pair (Primrec₂.comp Primrec.nat_mul Primrec.id Primrec.id) (Primrec.const [])
    · refine Primrec₂.comp Primrec.list_append (Primrec.const _) ?_
      refine Primrec₂.comp Primrec.list_cons ?_ (Primrec.const [])
      exact Primrec.pair (Primrec₂.comp Primrec.nat_mul (Primrec.const 2) Primrec.id)
        (Primrec.const [0])
  have he : specialize e = fun n : ℕ => ((lhsFixed e ++ [(n * n, ([] : List ℕ))] : NPoly ℕ),
      (rhsFixed e ++ [(2 * n, [0])] : NPoly ℕ)) := funext (specialize_eq e)
  rw [he]
  exact h.to_comp

/-- An undecidable computably enumerable predicate on `ℕ`: the halting problem for the
`n`-th partial recursive code on input `0`. -/
def Halt (n : ℕ) : Prop :=
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0).Dom

lemma halt_re : REPred Halt :=
  (ComputablePred.halting_problem_re 0).comp (Computable.ofNat Nat.Partrec.Code)

lemma halt_not_computable : ¬ ComputablePred Halt := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.mpr
    ⟨fun c => f (Encodable.encode c), hf.comp Computable.encode, ?_⟩)
  funext c
  have h2 := congrFun hfe (Encodable.encode c)
  simp only [Halt, Denumerable.ofNat_encode] at h2
  exact h2

/-!
### Solvability is computably enumerable

The easy half of the characterisation: one can search for a solution, so solvability of
Diophantine equations is a computably enumerable predicate.
-/

/-- Value of a monomial's variable list at the assignment given by a list of values. -/
def prodAt (l : List ℕ) (xs : List ℕ) : ℕ := xs.foldr (fun i s => l.getD i 0 * s) 1

/-- Value of a polynomial at the assignment given by a list of values (variables beyond
the length of the list get the value `0`). -/
def evalL (p : NPoly ℕ) (l : List ℕ) : ℕ := p.foldr (fun m s => m.1 * prodAt l m.2 + s) 0

lemma primrec_prodAt : Primrec₂ prodAt := by
  have h1 := (Primrec.list_getD (0 : ℕ)).comp
    (Primrec.fst.comp (Primrec.fst : Primrec fun a : (List ℕ × List ℕ) × (ℕ × ℕ) => a.1))
    (Primrec.fst.comp (Primrec.snd : Primrec fun a : (List ℕ × List ℕ) × (ℕ × ℕ) => a.2))
  have hh := Primrec₂.comp Primrec.nat_mul h1
    (Primrec.snd.comp (Primrec.snd : Primrec fun a : (List ℕ × List ℕ) × (ℕ × ℕ) => a.2))
  unfold Primrec₂ prodAt
  exact Primrec.list_foldr (f := fun a : List ℕ × List ℕ => a.2) (g := fun _ => (1 : ℕ))
    (h := fun a p => List.getD a.1 p.1 0 * p.2) Primrec.snd (Primrec.const 1) hh

lemma primrec_evalL : Primrec₂ evalL := by
  unfold Primrec₂ evalL
  refine Primrec.list_foldr (f := fun a : NPoly ℕ × List ℕ => a.1)
    (g := fun _ => (0 : ℕ)) (h := fun a m => m.1.1 * prodAt a.2 m.1.2 + m.2)
    Primrec.fst (Primrec.const 0) ?_
  refine Primrec₂.comp Primrec.nat_add ?_ (Primrec.snd.comp Primrec.snd)
  refine Primrec₂.comp Primrec.nat_mul (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) ?_
  exact Primrec₂.comp primrec_prodAt (Primrec.snd.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))

lemma prodAt_eq (l xs : List ℕ) : prodAt l xs = (xs.map fun i => l.getD i 0).prod := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      simp only [prodAt, List.foldr_cons, List.map_cons, List.prod_cons] at *
      rw [ih]

lemma evalL_eq (p : NPoly ℕ) (l : List ℕ) : evalL p l = eval p (fun i => l.getD i 0) := by
  induction p with
  | nil => rfl
  | cons m p ih => simp only [evalL, List.foldr_cons, eval_cons, evalMon, prodAt_eq] at *; rw [ih]

lemma mem_le_foldr_max : ∀ (l : List ℕ), ∀ j ∈ l, j ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact le_max_left _ _
      · exact le_trans (ih j hj) (le_max_right _ _)

/-- An equation is solvable iff it has a solution given by a finite list of values. -/
lemma solvable_iff_exists_list (e : Eqn) :
    Solvable e ↔ ∃ l : List ℕ, evalL e.1 l = evalL e.2 l := by
  constructor
  · rintro ⟨v, hv⟩
    set N := (vars e.1 ++ vars e.2).foldr max 0 + 1 with hN
    refine ⟨(List.range N).map v, ?_⟩
    have key : ∀ p : NPoly ℕ, (∀ j ∈ vars p, j < N) →
        evalL p ((List.range N).map v) = eval p v := by
      intro p hp
      rw [evalL_eq]
      refine eval_congr fun j hj => ?_
      have hjN : j < N := hp j hj
      have hlen : j < ((List.range N).map v).length := by simpa using hjN
      rw [List.getD_eq_getElem _ _ hlen]
      simp
    have h1 : ∀ j ∈ vars e.1, j < N := fun j hj =>
      Nat.lt_succ_of_le (mem_le_foldr_max _ j (by simp [List.mem_append, hj]))
    have h2 : ∀ j ∈ vars e.2, j < N := fun j hj =>
      Nat.lt_succ_of_le (mem_le_foldr_max _ j (by simp [List.mem_append, hj]))
    rw [key e.1 h1, key e.2 h2, hv]
  · rintro ⟨l, hl⟩
    exact ⟨fun i => l.getD i 0, by rw [← evalL_eq, ← evalL_eq]; exact hl⟩

/-- **Hilbert's tenth problem is semi-decidable**: solvability of Diophantine equations is
a computably enumerable predicate. -/
theorem solvable_re : REPred Solvable := by
  have hcomp : Computable₂ fun (e : Eqn) (k : ℕ) =>
      decide (evalL e.1 (Denumerable.ofNat (List ℕ) k)
        = evalL e.2 (Denumerable.ofNat (List ℕ) k)) := by
    have hk : Primrec fun x : Eqn × ℕ => Denumerable.ofNat (List ℕ) x.2 :=
      (Primrec.ofNat (List ℕ)).comp Primrec.snd
    have heq : Primrec₂ fun a b : ℕ => decide (a = b) := by
      obtain ⟨_, h⟩ := Primrec.eq (α := ℕ)
      refine h.of_eq fun a => ?_
      congr 1
    have h1 := Primrec₂.comp primrec_evalL (Primrec.fst.comp Primrec.fst) hk
    have h2 := Primrec₂.comp primrec_evalL (Primrec.snd.comp Primrec.fst) hk
    exact (Primrec₂.comp heq h1 h2).to_comp
  have hdom := (Partrec.rfind (Computable₂.partrec₂ hcomp)).dom_re
  refine hdom.of_eq fun e => ?_
  rw [Nat.rfind_dom']
  rw [solvable_iff_exists_list]
  constructor
  · rintro ⟨k, hk, -⟩
    refine ⟨Denumerable.ofNat (List ℕ) k, ?_⟩
    simpa using hk
  · rintro ⟨l, hl⟩
    refine ⟨Encodable.encode l, ?_, fun {m} _ => trivial⟩
    simp [Denumerable.ofNat_encode, hl]

/-- Any Diophantine predicate on `ℕ` reduces to Hilbert's tenth problem: hence if some
Diophantine predicate is undecidable, so is Hilbert's tenth problem. -/
theorem undecidable_of_dioph {S : ℕ → Prop} (hS : ¬ ComputablePred S)
    (hd : Dioph {v : Unit → ℕ | S (v ())}) : ¬ ComputablePred Solvable := by
  intro hsol
  obtain ⟨e, he⟩ := dioph_to_eqn hd
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp hsol
  refine hS (ComputablePred.computable_iff.mpr
    ⟨fun n => f (specialize e n), hf.comp (computable_specialize e), ?_⟩)
  funext n
  have h1 : S n ↔ Solvable (specialize e n) := by
    rw [solvable_specialize, he n]
  have h2 := congrFun hfe (specialize e n)
  rw [← h2]
  exact propext h1

end Hilbert10

open Hilbert10 in
/-- **Hilbert's tenth problem is undecidable**: granted the MRDP theorem (every computably
enumerable predicate on `ℕ` is Diophantine), there is no algorithm deciding whether a
Diophantine equation `P = Q` has a solution in natural numbers.

The proof reduces the halting problem to Hilbert's tenth problem: MRDP turns the halting
set into a Diophantine equation with a parameter, and substituting the parameter is a
primitive recursive operation on equations.  In fact only the Diophantineness of the
halting set is used, see `CS.Hilbert10.undecidable_of_dioph`. -/
theorem hilbert10_undecidable (mrdp : MRDP) : ¬ ComputablePred Solvable :=
  undecidable_of_dioph halt_not_computable (mrdp Halt halt_re)

end CS

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

