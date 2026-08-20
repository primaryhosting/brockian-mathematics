/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The first-order language of arithmetic, with function symbols `0, 1, +, *`
and no relation symbols. -/
def arith : Language where
  Functions := arithFunc
  Relations := fun _ => Empty

/-- The standard model: the natural numbers, interpreting the symbols as usual. -/
instance : arith.Structure ℕ where
  funMap {n} f v :=
    match n, f with
    | _, .zero => 0
    | _, .one => 1
    | _, .add => v 0 + v 1
    | _, .mul => v 0 * v 1
  RelMap {n} r := nomatch r

/-- An encoding of the function symbols of arithmetic as natural numbers. -/
private def arithFuncEnc : (Σ l, arith.Functions l) → ℕ
  | ⟨_, .zero⟩ => 0
  | ⟨_, .one⟩ => 1
  | ⟨_, .add⟩ => 2
  | ⟨_, .mul⟩ => 3

private theorem arithFuncEnc_injective : Function.Injective arithFuncEnc := by
  rintro ⟨_, (_ | _ | _ | _)⟩ ⟨_, (_ | _ | _ | _)⟩ h <;> simp_all [arithFuncEnc]

instance : Countable arith.Symbols := by
  have h1 : Countable (Σ l, arith.Functions l) := arithFuncEnc_injective.countable
  have h2 : Countable (Σ l, arith.Relations l) := by
    refine Function.Injective.countable (f := fun x => (nomatch x.2 : ℕ)) ?_
    rintro ⟨_, r⟩; exact nomatch r
  exact instCountableSum

/-! ## Arithmetical definability -/

/-- A set of natural numbers is *arithmetical* if it is the extension of some first-order
formula of the language of arithmetic with one free variable, interpreted in the standard
model `ℕ`. -/
def IsArithmetical (S : Set ℕ) : Prop :=
  ∃ φ : arith.Formula (Fin 1), ∀ n : ℕ, n ∈ S ↔ φ.Realize (fun _ => n)

/-- A binary relation on the natural numbers is *arithmetical* if it is the extension of some
first-order formula of the language of arithmetic with two free variables, interpreted in the
standard model `ℕ`. -/
def IsArithmetical₂ (R : Set (ℕ × ℕ)) : Prop :=
  ∃ φ : arith.Formula (Fin 2), ∀ v : Fin 2 → ℕ, (v 0, v 1) ∈ R ↔ φ.Realize v

/-! ## Gödel numberings and the satisfaction relation -/

/-- A *Gödel numbering* of the arithmetical formulas in one free variable is any surjection
from `ℕ` onto those formulas. (Formulas form a countable set, so such numberings exist; see
`exists_goedelNumbering`.) -/
def IsGoedelNumbering (num : ℕ → arith.Formula (Fin 1)) : Prop :=
  Function.Surjective num

theorem exists_goedelNumbering : ∃ num : ℕ → arith.Formula (Fin 1), IsGoedelNumbering num :=
  exists_surjective_nat _

/-- *Arithmetical truth*, relative to a Gödel numbering `num`: the set of pairs `(e, n)` such
that the formula with code `e` is true in the standard model `ℕ` of the number `n`.
This is Tarski's satisfaction relation for the language of arithmetic. -/
def truthSet (num : ℕ → arith.Formula (Fin 1)) : Set (ℕ × ℕ) :=
  {p | (num p.1).Realize (fun _ => p.2)}

/-! ## Tarski's undefinability theorem -/

/-- The diagonal of an arithmetical binary relation, complemented, is again arithmetical. -/
theorem isArithmetical_compl_diagonal {R : Set (ℕ × ℕ)} (hR : IsArithmetical₂ R) :
    IsArithmetical {n : ℕ | (n, n) ∉ R} := by
  obtain ⟨φ, hφ⟩ := hR
  refine ⟨(φ.relabel (fun _ => (0 : Fin 1))).not, fun n => ?_⟩
  have h := hφ (fun _ => n)
  simp only [Set.mem_setOf_eq, Formula.realize_not, Formula.realize_relabel] at *
  rw [show ((fun _ => n) ∘ (fun _ : Fin 2 => (0 : Fin 1))) = (fun _ : Fin 2 => n) from rfl]
  exact not_congr h

/-- **Tarski's undefinability theorem** (universality form): no arithmetical binary relation is
universal for the arithmetical sets, i.e. no single arithmetical relation `U` has the property
that every arithmetical set of naturals occurs as a section `{n | (a, n) ∈ U}` of `U`. -/
theorem no_universal_arithmetical_relation :
    ¬ ∃ U : Set (ℕ × ℕ), IsArithmetical₂ U ∧
      ∀ S : Set ℕ, IsArithmetical S → ∃ a : ℕ, S = {n | (a, n) ∈ U} := by
  rintro ⟨U, hU, huniv⟩
  obtain ⟨a, ha⟩ := huniv _ (isArithmetical_compl_diagonal hU)
  have : (a, a) ∉ U ↔ (a, a) ∈ U := by
    constructor
    · intro h; exact (Set.ext_iff.1 ha a).1 h
    · intro h hc; exact hc h
  tauto

/-- **Tarski's undefinability theorem.**  Arithmetical truth is not arithmetically definable:
for *any* Gödel numbering `num` of the formulas of arithmetic in one free variable, the
satisfaction relation `{(e, n) | ℕ ⊨ (num e)(n)}` is not definable by a formula of arithmetic
in the standard model `ℕ`. -/
theorem Tarski_undefinability (num : ℕ → arith.Formula (Fin 1)) (hnum : IsGoedelNumbering num) :
    ¬ IsArithmetical₂ (truthSet num) := by
  intro hT
  obtain ⟨ψ, hψ⟩ := isArithmetical_compl_diagonal hT
  obtain ⟨e, he⟩ := hnum ψ
  have key : (e, e) ∉ truthSet num ↔ (e, e) ∈ truthSet num := by
    have h1 : e ∈ {n : ℕ | (n, n) ∉ truthSet num} ↔ ψ.Realize (fun _ => e) := hψ e
    have h2 : (e, e) ∈ truthSet num ↔ ψ.Realize (fun _ => e) := by
      simp only [truthSet, Set.mem_setOf_eq, he]
    rw [Set.mem_setOf_eq] at h1
    rw [h1, h2]
  tauto

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

