/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## Machine model

We work with a *non-uniform* space-bounded machine model.  A machine works on inputs of one
fixed length; a language belongs to a space class if for every input length there is a machine
of the appropriate size deciding the language on inputs of that length.

A machine is described by its set of configurations `Cfg` (which is the whole memory of the
machine: the space used is `log₂ (card Cfg)`), a designated start configuration, a function
`head` telling which position of the (read-only) input is currently scanned, and a transition
which may depend on the current configuration and on the single input bit that is being read.
Note that the machine has *no* other access to the input, which is what makes the space measure
meaningful. -/

/-- The `i`-th bit of an input word; `false` beyond the end of the word. -/

lemma NSM.accepts_iff_reach (x : List Bool) :
    M.Accepts x ↔
      Relation.ReflTransGen (fun a b => M.E' x a b = true) (some M.start) none := by
  classical
  constructor
  · rintro ⟨c, hacc, hpath⟩
    have lift : ∀ a b : M.Cfg, Relation.ReflTransGen (M.Edge x) a b →
        Relation.ReflTransGen (fun a b => M.E' x a b = true) (some a) (some b) := by
      intro a b h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail hbc
    exact (lift _ _ hpath).tail (by simpa [NSM.E', NSM.edge'] using hacc)
  · intro h
    have key : ∀ c : Option M.Cfg,
        Relation.ReflTransGen (fun a b => M.E' x a b = true) (some M.start) c →
        ((∀ a, c = some a → Relation.ReflTransGen (M.Edge x) M.start a) ∧
          (c = none → M.Accepts x)) := by
      intro c hc
      induction hc with
      | refl =>
          refine ⟨fun a ha => ?_, fun ha => by cases ha⟩
          cases ha; exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
          cases b with
          | none => simp [NSM.E', NSM.edge'] at hbc
          | some a =>
              have hpa : Relation.ReflTransGen (M.Edge x) M.start a := ih.1 a rfl
              cases c with
              | none =>
                  refine ⟨fun z hz => (by cases hz), fun _ => ?_⟩
                  exact ⟨a, by simpa [NSM.E', NSM.edge'] using hbc, hpa⟩
              | some e =>
                  refine ⟨fun z hz => ?_, fun hz => (by cases hz)⟩
                  cases hz
                  exact hpa.tail (by simpa [NSM.E', NSM.edge', NSM.Edge, NSM.head'] using hbc)
    exact (key none h).2 rfl

end Sink

/-! ## Finiteness of bounded-length lists -/

section BoundedLists

variable {α : Type} [Fintype α] (n : ℕ)

/-- Encoding of a list of length at most `n` by its optional entries. -/
