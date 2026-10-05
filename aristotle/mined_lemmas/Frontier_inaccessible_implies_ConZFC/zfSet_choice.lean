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

