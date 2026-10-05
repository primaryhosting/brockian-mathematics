/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4

We show that the two-colour Ramsey number `R(4,4)` equals `18`:

* every symmetric two-colouring of the edges of the complete graph on `18` vertices
  contains a monochromatic set of `4` vertices;
* there is a symmetric two-colouring of the edges of the complete graph on `17` vertices
  (the Paley graph of order `17`) with no monochromatic set of `4` vertices.
-/

namespace Math

open Finset

/-- `MonoSet f b S` says that every pair of distinct vertices of `S` receives colour `b`. -/

lemma paley_no_mono_finset {S : Finset (Fin 17)} (h : S.card = 4) (col : Bool) :
    ¬ MonoSet paleyColor col S := by
  intro hm
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := exists_four_of_card_eq_four h
  have ha : a ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have hb : b ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have hc : c ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have hd : d ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  exact paley_no_mono4 a b c d hab hac had hbc hbd hcd col
    ⟨hm a ha b hb hab, hm a ha c hc hac, hm a ha d hd had,
      hm b hb c hc hbc, hm b hb d hd hbd, hm c hc d hd hcd⟩

