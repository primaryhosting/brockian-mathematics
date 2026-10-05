/-
Models of ZFC given by suitable classes of ZFC sets.
-/
import RequestProject.SetLanguage

/-!
# Classes of sets that model ZFC

We isolate a set of closure conditions on a class `P : ZFSet.{u} → Prop`
(`Frontier.IsZFCClass`) which guarantee that the structure with domain `{x : ZFSet // P x}`
and the real membership relation is a model of the first-order theory `Frontier.ZFC`.

The conditions are: transitivity, closure under pairing, unions, power sets, the presence of
`ω`, and closure under (second-order) replacement.

The class of *all* sets satisfies these conditions, so `ZFSet.{u}` itself is a model of ZFC.
-/

universe u w

namespace Frontier

open FirstOrder Language ZFSet

/-- The `setLang`-structure on a type equipped with a binary relation. -/

theorem not_models_ZFC_of_subsingleton {M : Type v} [setLang.{u}.Structure M] [Subsingleton M]
    [M ⊨ ZFC.{u}] : False := by
  have h : M ⊨ infAx.{u} := Theory.realize_sentence_of_mem ZFC (by
    simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto)
  rw [realize_infAx] at h
  obtain ⟨w, ⟨e, hew, he⟩, -⟩ := h
  rw [Subsingleton.elim w e] at hew
  exact he e hew

end Frontier

/-
The first-order language of set theory and the axioms of ZFC.
-/
import Mathlib

/-!
# The first-order language of set theory, and the theory ZFC

We define the first-order language `Frontier.setLang` with a single binary relation symbol `∈`,
and the theory `Frontier.ZFC` consisting of the usual axioms of Zermelo–Fraenkel set theory
with choice:

* extensionality, foundation (regularity), pairing, union, power set, infinity, choice
  (in Zermelo's "multiplicative axiom" form, which needs no coding of ordered pairs), and
* the separation and replacement schemes, one axiom for each first-order formula with
  finitely many parameters.

For each axiom we also prove a `realize_*` lemma unfolding what it means for a structure to
satisfy it.
-/

universe u w

namespace Frontier

open FirstOrder Language BoundedFormula

/-- The relation symbols of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/
