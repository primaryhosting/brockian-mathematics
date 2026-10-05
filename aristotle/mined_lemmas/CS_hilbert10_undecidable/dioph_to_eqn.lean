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
