import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset

/-! ## Upper bound: every 2-colouring of `K₁₈` has a monochromatic `K₄`

We phrase a 2-colouring of the edges of a complete graph as a simple graph `G`
(the "red" edges); the "blue" edges are the edges of the complement `Gᶜ`.
-/

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside the finite set `s`. -/

lemma paley_no_clique_four {n : ℕ} (hn : n ≤ 17) (s : Finset (Fin n))
    (hs : (paleyGraph n).IsNClique 4 s ∨ (paleyGraph n)ᶜ.IsNClique 4 s) : False := by
  have hcard : s.card = 4 := by rcases hs with h | h; exacts [h.2, h.2]
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hcard
  have hma : a ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hmb : b ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hmc : c ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hmd : d ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hlt : ∀ i : Fin n, (i : ℕ) < 17 := fun i => lt_of_lt_of_le i.isLt hn
  have hne : ∀ {i j : Fin n}, i ≠ j → (i : ℕ) ≠ (j : ℕ) := by
    intro i j h hv
    exact h (Fin.ext hv)
  rcases hs with ⟨hcl, -⟩ | ⟨hcl, -⟩
  · refine paley_no_mono_four a b c d (hlt a) (hlt b) (hlt c) (hlt d) (hne hab) (hne hac)
      (hne had) (hne hbc) (hne hbd) (hne hcd) true
      (hcl hma hmb hab).2 (hcl hma hmc hac).2 (hcl hma hmd had).2
      (hcl hmb hmc hbc).2 (hcl hmb hmd hbd).2 (hcl hmc hmd hcd).2
  · have key : ∀ {i j : Fin n}, i ≠ j → (paleyGraph n)ᶜ.Adj i j → padj i.val j.val = false := by
      intro i j hij h
      simp only [SimpleGraph.compl_adj, paleyGraph, hij, ne_eq, not_false_eq_true,
        Bool.not_eq_true, true_and] at h
      exact h
    exact paley_no_mono_four a b c d (hlt a) (hlt b) (hlt c) (hlt d) (hne hab) (hne hac)
      (hne had) (hne hbc) (hne hbd) (hne hcd) false
      (key hab (hcl hma hmb hab)) (key hac (hcl hma hmc hac)) (key had (hcl hma hmd had))
      (key hbc (hcl hmb hmc hbc)) (key hbd (hcl hmb hmd hbd)) (key hcd (hcl hmc hmd hcd))

/-! ## The Ramsey number `R(4,4) = 18` -/

/-- **The two-colour Ramsey number `R(4,4)` equals `18`.**
Reading a 2-colouring of the edges of the complete graph on `n` vertices as a simple graph `G`
(the edges of the first colour) together with its complement `Gᶜ` (the second colour),
`18` is the least `n` such that every 2-colouring of `Kₙ` contains a monochromatic `K₄`. -/
