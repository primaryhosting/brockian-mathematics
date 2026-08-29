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

## Contents

Hilbert's tenth problem asks for an algorithm deciding whether a polynomial equation with
integer coefficients has a solution.  Here it is formalised in its standard arithmetic form:
a *Diophantine equation* is a pair of polynomials `p`, `q` with natural number coefficients
(concretely, lists of monomials, so that equations are objects of a `Primcodable` type and the
decision problem makes sense), and the question is whether `p = q` has a solution in natural
numbers (`CS.Solvable`).  Every polynomial equation with integer coefficients can be put into
this shape by moving the negative terms to the other side.

* `CS.hilbert10_re` : unconditionally, the set of solvable Diophantine equations is
  recursively enumerable, and `CS.IsDioph.re`: every Diophantine set of naturals is r.e.
* `CS.hilbert10_undecidable` : granting the MRDP theorem `CS.MRDP` — the converse
  direction, that every r.e. set of naturals is Diophantine — Diophantine solvability is not
  decidable.  The reduction of the halting problem for partial recursive functions to
  Diophantine solvability (substitution of the input into the parameter of a Diophantine
  definition, and its computability) is carried out in full.

The number-theoretic heart of MRDP itself (Matiyasevich's theorem that exponentiation is
Diophantine, and the elimination of bounded universal quantifiers) is not available in
Mathlib in the form needed here, so `CS.MRDP` is taken as an explicit hypothesis of the
undecidability theorem rather than proved.
-/

namespace CS

/-! ## Syntax of Diophantine equations

A monomial is a coefficient together with a list of exponents: the `i`-th entry of the list is
the exponent of the variable `xᵢ` (variables beyond the length of the list have exponent `0`).
A polynomial is a list of monomials, interpreted as their sum.  A Diophantine equation is a
pair of such polynomials; it is *solvable* if the two sides can be made equal by some
assignment of natural numbers to the variables. -/

/-- A monomial: a coefficient and the list of exponents of the variables. -/
abbrev Monomial : Type := ℕ × List ℕ

/-- A polynomial with natural number coefficients, as a list of monomials. -/
abbrev DioPoly : Type := List Monomial

/-- `scons n x` is the assignment sending variable `0` to `n` and variable `i+1` to `x i`. -/
def scons (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => n
  | (i + 1) => x i

/-- Value of a product of powers `x₀ ^ e₀ * x₁ ^ e₁ * ⋯` given the list of exponents. -/
def evalExps : List ℕ → (ℕ → ℕ) → ℕ
  | [], _ => 1
  | e :: es, x => x 0 ^ e * evalExps es (fun i => x (i + 1))

/-- Value of a monomial under an assignment. -/
def evalMon (m : Monomial) (x : ℕ → ℕ) : ℕ := m.1 * evalExps m.2 x

/-- Value of a polynomial under an assignment. -/
def evalPoly (p : DioPoly) (x : ℕ → ℕ) : ℕ := (p.map (fun m => evalMon m x)).sum

/-- Substituting the constant `n` for the variable `x₀` (and shifting the other variables). -/
def substZero (n : ℕ) (p : DioPoly) : DioPoly :=
  p.map (fun m => (m.1 * n ^ m.2.headI, m.2.tail))

/-- **Hilbert's tenth problem** as a decision problem: given a pair of polynomials with natural
coefficients, does the equation `p = q` have a solution in natural numbers? -/
def Solvable (e : DioPoly × DioPoly) : Prop := ∃ x : ℕ → ℕ, evalPoly e.1 x = evalPoly e.2 x

/-- A set of naturals is *Diophantine* if it is the solution set (in the parameter `x₀`) of a
Diophantine equation. -/
def IsDioph (S : Set ℕ) : Prop :=
  ∃ p q : DioPoly, ∀ n, n ∈ S ↔ ∃ x : ℕ → ℕ, evalPoly p (scons n x) = evalPoly q (scons n x)

/-- The **MRDP theorem** (Matiyasevich–Robinson–Davis–Putnam): every recursively enumerable set
of natural numbers is Diophantine. -/
def MRDP : Prop := ∀ S : Set ℕ, REPred (fun n => n ∈ S) → IsDioph S

/-! ## Substitution -/

theorem evalPoly_substZero (n : ℕ) (p : DioPoly) (x : ℕ → ℕ) :
    evalPoly (substZero n p) x = evalPoly p (scons n x) := by
  simp only [evalPoly, substZero, List.map_map]
  congr 1
  refine List.map_congr_left ?_
  rintro ⟨c, es⟩ -
  cases es with
  | nil => simp [evalMon, evalExps]
  | cons e es =>
      simp only [evalMon, evalExps, Function.comp_apply, List.headI_cons, List.tail_cons]
      have : (fun i => scons n x (i + 1)) = x := rfl
      rw [this]
      simp [scons]
      ring

/-! ## Computability of the reduction -/

theorem primrec_pow : Primrec₂ (fun a b : ℕ => a ^ b) := by
  have h : Primrec₂ (fun a n : ℕ => Nat.rec (motive := fun _ => ℕ) 1
      (fun _ IH => a * IH) n) :=
    Primrec.nat_rec (f := fun _ : ℕ => (1 : ℕ)) (g := fun a p => a * p.2)
      (Primrec.const 1)
      (Primrec.nat_mul.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun a b => ?_
  induction b with
  | zero => simp
  | succ k ih => simp [pow_succ, ih]; ring

theorem computable_substZero (p : DioPoly) : Computable (fun n : ℕ => substZero n p) := by
  have hg : Primrec₂ (fun (n : ℕ) (m : Monomial) => (m.1 * n ^ m.2.headI, m.2.tail)) := by
    refine Primrec₂.mk (Primrec.pair ?_ ?_)
    · exact Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
        (primrec_pow.comp Primrec.fst
          (Primrec.list_headI.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_map (Primrec.const p) hg).to_comp

/-! ## Undecidability -/

/-- **Hilbert's tenth problem is undecidable**: assuming the MRDP theorem (every recursively
enumerable set of naturals is Diophantine), there is no algorithm deciding whether a
Diophantine equation with natural number coefficients has a solution in natural numbers. -/
theorem hilbert10_undecidable (hMRDP : MRDP) : ¬ ComputablePred Solvable := by
  intro hSolv
  -- the halting set, transported along the numbering of partial recursive codes
  set S : Set ℕ := {c | (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code c) 0).Dom}
    with hS
  have hre : REPred (fun n => n ∈ S) :=
    (Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code)
      (Computable.const 0)).dom_re
  obtain ⟨p, q, hpq⟩ := hMRDP S hre
  obtain ⟨f, hf, hfS⟩ := ComputablePred.computable_iff.1 hSolv
  have hF : Computable (fun n : ℕ => ((substZero n p, substZero n q) : DioPoly × DioPoly)) :=
    Computable.pair (computable_substZero p) (computable_substZero q)
  have key : ∀ n : ℕ, (n ∈ S ↔ f (substZero n p, substZero n q) = true) := by
    intro n
    have h2 : Solvable (substZero n p, substZero n q) ↔
        f (substZero n p, substZero n q) = true := by
      rw [hfS]
    rw [← h2]
    simpa only [Solvable, evalPoly_substZero] using hpq n
  -- hence the halting problem would be decidable
  have hcomp : ComputablePred (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) := by
    refine ComputablePred.computable_iff.2
      ⟨fun c => f (substZero (Encodable.encode c) p, substZero (Encodable.encode c) q),
        hf.comp (hF.comp Computable.encode), ?_⟩
    funext c
    have := key (Encodable.encode c)
    simp only [hS, Set.mem_setOf_eq, Denumerable.ofNat_encode] at this
    simpa using this
  exact ComputablePred.halting_problem 0 hcomp

/-! ## Hilbert's tenth problem is semi-decidable

Unconditionally, the set of solvable Diophantine equations is recursively enumerable: one can
search through all candidate solutions.  (Together with the theorem above this says that
Hilbert's tenth problem is r.e. but, granting MRDP, not co-r.e.) -/

/-- Evaluation of the exponent list as a product over the range of its length. -/
theorem evalExps_eq_range (es : List ℕ) (x : ℕ → ℕ) :
    evalExps es x = ((List.range es.length).map (fun i => x i ^ es.getD i 0)).prod := by
  induction es generalizing x with
  | nil => simp [evalExps]
  | cons e es ih =>
      simp only [evalExps, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.prod_cons]
      rw [ih]
      simp [Function.comp_def]

/-- An upper bound for the indices of the variables occurring in a polynomial. -/
def varBound (p : DioPoly) : ℕ := (p.map (fun m => m.2.length)).foldr max 0

theorem length_le_varBound {p : DioPoly} {m : Monomial} (hm : m ∈ p) :
    m.2.length ≤ varBound p := by
  induction p with
  | nil => cases hm
  | cons a p ih =>
      rcases List.mem_cons.1 hm with h | h
      · subst h; simp [varBound]
      · exact le_trans (ih h) (by simp [varBound])

theorem evalPoly_congr (p : DioPoly) {x y : ℕ → ℕ} (h : ∀ i < varBound p, x i = y i) :
    evalPoly p x = evalPoly p y := by
  simp only [evalPoly]
  congr 1
  refine List.map_congr_left ?_
  intro m hm
  simp only [evalMon, evalExps_eq_range]
  congr 2
  refine List.map_congr_left ?_
  intro i hi
  rw [h i (lt_of_lt_of_le (List.mem_range.1 hi) (length_le_varBound hm))]

/-- Evaluation of a polynomial at an assignment given by a list (missing entries are `0`). -/
def evalPolyL (p : DioPoly) (l : List ℕ) : ℕ :=
  (p.map (fun m => m.1 * ((List.range m.2.length).map
    (fun i => (l.getD i 0) ^ (m.2.getD i 0))).prod)).sum

theorem evalPolyL_eq (p : DioPoly) (l : List ℕ) :
    evalPolyL p l = evalPoly p (fun i => l.getD i 0) := by
  simp [evalPolyL, evalPoly, evalMon, evalExps_eq_range]

theorem solvable_iff_exists_list (e : DioPoly × DioPoly) :
    Solvable e ↔ ∃ l : List ℕ, evalPolyL e.1 l = evalPolyL e.2 l := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(List.range (max (varBound e.1) (varBound e.2))).map x, ?_⟩
    have hval : ∀ i < max (varBound e.1) (varBound e.2),
        ((List.range (max (varBound e.1) (varBound e.2))).map x).getD i 0 = x i := by
      intro i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rfl
    rw [evalPolyL_eq, evalPolyL_eq,
      evalPoly_congr e.1 (y := x) (fun i hi => hval i (lt_of_lt_of_le hi (le_max_left _ _))),
      evalPoly_congr e.2 (y := x) (fun i hi => hval i (lt_of_lt_of_le hi (le_max_right _ _)))]
    exact hx
  · rintro ⟨l, hl⟩
    exact ⟨fun i => l.getD i 0, by rw [← evalPolyL_eq, ← evalPolyL_eq]; exact hl⟩

theorem primrec_listProd : Primrec (fun l : List ℕ => l.prod) :=
  (Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ => 1) (h := fun _ p => p.1 * p.2)
    Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))).of_eq fun l => by rw [List.prod_eq_foldr]

theorem primrec_listSum : Primrec (fun l : List ℕ => l.sum) :=
  (Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ => 0) (h := fun _ p => p.1 + p.2)
    Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))).of_eq fun l => by rw [List.sum_eq_foldr]

theorem primrec_evalPolyL : Primrec₂ (fun (p : DioPoly) (l : List ℕ) => evalPolyL p l) := by
  have hgetD : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l.getD i 0) := by
    have h : Primrec₂ (fun (l : List ℕ) (i : ℕ) => (l[i]?).getD 0) :=
      Primrec.option_getD.comp₂ Primrec.list_getElem? (Primrec₂.const 0)
    exact h.of_eq fun l i => by simp [List.getD_eq_getElem?_getD]
  have hmon : Primrec (fun a : (DioPoly × List ℕ) × Monomial =>
      a.2.1 * ((List.range a.2.2.length).map
        (fun i => (a.1.2.getD i 0) ^ (a.2.2.getD i 0))).prod) := by
    refine Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (primrec_listProd.comp ?_)
    refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))) ?_
    exact Primrec₂.mk (primrec_pow.comp
      (hgetD.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (hgetD.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  exact Primrec₂.mk (primrec_listSum.comp (Primrec.list_map Primrec.fst hmon))

/-- **Hilbert's tenth problem is semi-decidable**: the set of solvable Diophantine equations is
recursively enumerable. -/
theorem hilbert10_re : REPred Solvable := by
  have hdec : Computable₂ (fun (e : DioPoly × DioPoly) (k : ℕ) =>
      (evalPolyL e.1 (Denumerable.ofNat (List ℕ) k) ==
        evalPolyL e.2 (Denumerable.ofNat (List ℕ) k) : Bool)) := by
    have hl : Computable (fun (q : (DioPoly × DioPoly) × ℕ) =>
        Denumerable.ofNat (List ℕ) q.2) := (Computable.ofNat (List ℕ)).comp Computable.snd
    exact Primrec.beq.to_comp.comp
      (primrec_evalPolyL.to_comp.comp (Computable.fst.comp Computable.fst) hl)
      (primrec_evalPolyL.to_comp.comp (Computable.snd.comp Computable.fst) hl)
  have hp : Partrec (fun e : DioPoly × DioPoly => Nat.rfind (fun k =>
      ((evalPolyL e.1 (Denumerable.ofNat (List ℕ) k) ==
        evalPolyL e.2 (Denumerable.ofNat (List ℕ) k) : Bool) : Part Bool))) :=
    Partrec.rfind hdec.partrec₂
  refine (hp.dom_re).of_eq fun e => ?_
  rw [solvable_iff_exists_list, Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk, -⟩
    exact ⟨_, by simpa using hk⟩
  · rintro ⟨l, hl⟩
    exact ⟨Encodable.encode l, by simpa using hl, fun {m} _ => trivial⟩

/-- Every Diophantine set is recursively enumerable (the easy converse of MRDP). -/
theorem IsDioph.re {S : Set ℕ} (h : IsDioph S) : REPred (fun n => n ∈ S) := by
  obtain ⟨p, q, hpq⟩ := h
  have hF : Computable (fun n : ℕ => ((substZero n p, substZero n q) : DioPoly × DioPoly)) :=
    Computable.pair (computable_substZero p) (computable_substZero q)
  have h1 : REPred (fun n : ℕ => Solvable (substZero n p, substZero n q)) :=
    Partrec.comp hilbert10_re hF
  refine h1.of_eq fun n => ?_
  simp only [Solvable, evalPoly_substZero]
  exact (hpq n).symm

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

