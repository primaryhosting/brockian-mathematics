/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Statement: A consistent theory cannot prove its own reflection schema for an unprovable sentence (Löb-based).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
# Löb's theorem: a consistent theory cannot trust itself

We formalize, in an abstract but faithful setting, the statement that a consistent
theory cannot prove the *reflection principle* `Prov(⌜A⌝) → A` for a sentence `A`
that it does not prove.

The setting is an abstract theory over a type `S` of sentences, equipped with
implication, a provability predicate `Pr` (the internal formalization of
"is provable"), the Hilbert–Bernays–Löb derivability conditions, and the
diagonal (fixed point) lemma.  This is exactly the structure that Peano
arithmetic (or any consistent r.e. extension of it) provides, and it is enough
to derive Löb's theorem, hence the result.
-/

namespace Frontier

/-- An abstract theory with an internal provability predicate.

* `imp` is the implication connective of the language;
* `Pr s` is the sentence expressing "`s` is provable in the theory";
* `Thm s` means "`s` is a theorem of the theory".

The axioms are:
* closure of `Thm` under modus ponens, together with the two Hilbert axiom
  schemes `K` and `S` (i.e. the theory contains implicational propositional
  logic);
* the Hilbert–Bernays–Löb derivability conditions `hb1`, `hb2`, `hb3`;
* the diagonal lemma `diag`: for every formula `f` (with one free slot) there is
  a sentence `p` provably equivalent to `f` applied to (the code of) `Pr p`.
  Diagonalizing through `Pr` is what the arithmetical diagonal lemma provides:
  applying it to the formula `x ↦ f (Pr x)` yields such a `p`. -/
structure ProvabilityTheory (S : Type*) where
  /-- The implication connective. -/
  imp : S → S → S
  /-- The internal provability predicate. -/
  Pr : S → S
  /-- Theoremhood in the theory. -/
  Thm : S → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b : S}, Thm (imp a b) → Thm a → Thm b
  /-- Hilbert axiom scheme `K`. -/
  ax_K : ∀ a b : S, Thm (imp a (imp b a))
  /-- Hilbert axiom scheme `S`. -/
  ax_S : ∀ a b c : S, Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- First derivability condition: theorems are provably provable. -/
  hb1 : ∀ {a : S}, Thm a → Thm (Pr a)
  /-- Second derivability condition: internal modus ponens. -/
  hb2 : ∀ a b : S, Thm (imp (Pr (imp a b)) (imp (Pr a) (Pr b)))
  /-- Third derivability condition: provable provability is provably provable. -/
  hb3 : ∀ a : S, Thm (imp (Pr a) (Pr (Pr a)))
  /-- Diagonal lemma (fixed points through the provability predicate). -/
  diag : ∀ f : S → S, ∃ p : S, Thm (imp p (f (Pr p))) ∧ Thm (imp (f (Pr p)) p)

namespace ProvabilityTheory

variable {S : Type*} (T : ProvabilityTheory S)

/-- A theory is consistent if some sentence is not a theorem of it. -/
def Consistent : Prop := ∃ s : S, ¬ T.Thm s

/-- The reflection principle for `A`: "if `A` is provable, then `A`". -/
def reflection (A : S) : S := T.imp (T.Pr A) A

/-- Transitivity of implication inside the theory. -/
theorem imp_trans {a b c : S} (h₁ : T.Thm (T.imp a b)) (h₂ : T.Thm (T.imp b c)) :
    T.Thm (T.imp a c) :=
  T.mp (T.mp (T.ax_S a b c) (T.mp (T.ax_K (T.imp b c) a) h₂)) h₁

/-- Distribution of implication inside the theory. -/
theorem imp_dist {a b c : S} (h₁ : T.Thm (T.imp a (T.imp b c))) (h₂ : T.Thm (T.imp a b)) :
    T.Thm (T.imp a c) :=
  T.mp (T.mp (T.ax_S a b c) h₁) h₂

/-- **Löb's theorem**: if the theory proves its own reflection principle for `A`,
then it proves `A`. -/
theorem loeb (A : S) (h : T.Thm (T.reflection A)) : T.Thm A := by
  obtain ⟨p, hp₁, hp₂⟩ := T.diag (fun q => T.imp q A)
  -- `hp₁ : T ⊢ p → (Pr p → A)` and `hp₂ : T ⊢ (Pr p → A) → p`
  have h₃ : T.Thm (T.imp (T.Pr p) (T.Pr (T.imp (T.Pr p) A))) :=
    T.mp (T.hb2 _ _) (T.hb1 hp₁)
  have h₅ : T.Thm (T.imp (T.Pr p) (T.imp (T.Pr (T.Pr p)) (T.Pr A))) :=
    T.imp_trans h₃ (T.hb2 _ _)
  have h₆ : T.Thm (T.imp (T.Pr p) (T.Pr A)) := T.imp_dist h₅ (T.hb3 p)
  have h₇ : T.Thm (T.imp (T.Pr p) A) := T.imp_trans h₆ h
  exact T.mp h₇ (T.hb1 (T.mp hp₂ h₇))

/-- Conversely, a theory proving `A` proves the reflection principle for `A`. -/
theorem reflection_of_thm (A : S) (h : T.Thm A) : T.Thm (T.reflection A) :=
  T.mp (T.ax_K A (T.Pr A)) h

/-- Löb's theorem, as an equivalence: the theory proves the reflection principle
for `A` exactly when it proves `A`. -/
theorem thm_reflection_iff (A : S) : T.Thm (T.reflection A) ↔ T.Thm A :=
  ⟨T.loeb A, T.reflection_of_thm A⟩

end ProvabilityTheory

/-- **A consistent theory cannot trust itself.**

If `T` is a consistent theory satisfying the derivability conditions and the
diagonal lemma, and `A` is a sentence that `T` does not prove, then `T` does not
prove the reflection principle `Prov(⌜A⌝) → A` for `A`.

(The consistency hypothesis is stated because it is part of the classical
formulation; the proof only needs the unprovability of `A`, which by itself
already witnesses consistency.) -/
theorem loeb_no_self_trust {S : Type*} (T : ProvabilityTheory S) (A : S)
    (hcon : T.Consistent) (hunprov : ¬ T.Thm A) :
    ¬ T.Thm (T.reflection A) := by
  clear hcon
  exact fun h => hunprov (T.loeb A h)

/-- A consistent theory fails to prove reflection for *some* sentence; here the
consistency hypothesis is doing genuine work. -/
theorem loeb_no_uniform_reflection {S : Type*} (T : ProvabilityTheory S)
    (hcon : T.Consistent) : ∃ A : S, ¬ T.Thm (T.reflection A) := by
  obtain ⟨s, hs⟩ := hcon
  exact ⟨s, fun h => hs (T.loeb s h)⟩

/-- A sanity check that the axioms of `ProvabilityTheory` are satisfiable
*together with* consistency, so that the theorems above are not vacuous:
sentences are booleans, `Pr` is constantly `true`, and `Thm b` means `b = true`. -/
def boolModel : ProvabilityTheory Bool where
  imp a b := !a || b
  Pr _ := true
  Thm b := b = true
  mp {a b} h₁ h₂ := by revert h₁ h₂; cases a <;> cases b <;> simp
  ax_K a b := by cases a <;> cases b <;> simp
  ax_S a b c := by cases a <;> cases b <;> cases c <;> simp
  hb1 _ := rfl
  hb2 a b := by cases a <;> cases b <;> simp
  hb3 _ := rfl
  diag f := ⟨f true, by simp, by simp⟩

/-- The `boolModel` is consistent, so `loeb_no_self_trust` has instances. -/
theorem boolModel_consistent : boolModel.Consistent := ⟨false, by simp [boolModel]⟩

/-- `loeb_no_self_trust` applies non-vacuously: in `boolModel`, `false` is
unprovable, hence so is its reflection principle. -/
theorem boolModel_no_self_trust : ¬ boolModel.Thm (boolModel.reflection false) :=
  loeb_no_self_trust boolModel false boolModel_consistent (by simp [boolModel])

end Frontier

