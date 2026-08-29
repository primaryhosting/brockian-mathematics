/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an
`n`-element set. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

theorem kneserGraph_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n + 1) :
    (kneserGraph n k).Colorable (n + 2 - 2 * k) := by
  classical
  set m := n + 1 - 2 * k with hm
  have hne : ∀ s : KneserVertex n k, s.1.Nonempty := fun s => kneserVertex_nonempty hk s
  refine ⟨SimpleGraph.Coloring.mk
    (fun s => (⟨min m ((s.1.min' (hne s) : Fin n) : ℕ), by omega⟩ : Fin (n + 2 - 2 * k))) ?_⟩
  rintro s t ⟨-, hdisj⟩ hcol
  have hcol' : min m ((s.1.min' (hne s) : Fin n) : ℕ) = min m ((t.1.min' (hne t) : Fin n) : ℕ) := by
    simpa [Fin.ext_iff] using hcol
  set a : ℕ := ((s.1.min' (hne s) : Fin n) : ℕ) with ha
  set b : ℕ := ((t.1.min' (hne t) : Fin n) : ℕ) with hb
  by_cases hcase : a < m ∧ b < m
  · -- the two minima coincide, contradicting disjointness
    have hab : a = b := by omega
    have hsm : s.1.min' (hne s) ∈ s.1 := Finset.min'_mem _ _
    have htm : t.1.min' (hne t) ∈ t.1 := Finset.min'_mem _ _
    have : s.1.min' (hne s) = t.1.min' (hne t) := Fin.ext hab
    exact (Finset.disjoint_left.mp hdisj hsm) (this ▸ htm)
  · -- both sets live in the last `2k - 1` elements
    have hma : m ≤ a := by omega
    have hmb : m ≤ b := by omega
    have hsub : ∀ (u : Finset (Fin n)) (hu : u.Nonempty), m ≤ ((u.min' hu : Fin n) : ℕ) →
        u ⊆ (Finset.Ico m n).attachFin (by intro x hx; simp at hx; omega) := by
      intro u hu hmin x hx
      have hle : u.min' hu ≤ x := Finset.min'_le _ _ hx
      have : m ≤ (x : ℕ) := le_trans hmin hle
      simp only [Finset.mem_attachFin, Finset.mem_Ico]
      exact ⟨this, x.2⟩
    refine not_disjoint_of_card_lt s.2 t.2
      ((Finset.Ico m n).attachFin (by intro x hx; simp at hx; omega)) (hsub _ _ hma)
      (hsub _ _ hmb) ?_ hdisj
    rw [Finset.card_attachFin, Nat.card_Ico]
    omega

/-! ### The base case `k = 1`: the Kneser graph is the complete graph -/

