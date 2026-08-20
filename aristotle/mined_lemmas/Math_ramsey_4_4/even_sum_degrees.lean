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
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/

theorem even_sum_degrees {V : Type} (G : SimpleGraph V) (t : Finset V) :
    Even (∑ v ∈ t, {u ∈ t.erase v | G.Adj v u}.card) := by
  have hE : ∀ v ∈ t, {u ∈ t.erase v | G.Adj v u} = {u ∈ t | G.Adj v u} := by
    intro v _
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hu⟩, h⟩
      exact ⟨hu, h⟩
    · rintro ⟨hu, h⟩
      exact ⟨⟨(G.ne_of_adj h).symm, hu⟩, h⟩
  rw [Finset.sum_congr rfl (fun v hv => by rw [hE v hv]), ← ZMod.natCast_eq_zero_iff_even]
  push_cast
  have h1 : ∀ v ∈ t, (({u ∈ t | G.Adj v u}.card : ℕ) : ZMod 2)
      = ∑ u ∈ t, (if G.Adj v u then (1 : ZMod 2) else 0) := by
    intro v _
    rw [Finset.card_filter]
    push_cast
    simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Prod.fst_swap, Prod.snd_swap]
    by_cases h : G.Adj a.1 a.2
    · rw [if_pos h, if_pos (G.symm h)]
      decide
    · rw [if_neg h, if_neg (fun hh => h (G.symm hh))]
      simp
  · intro a _ hne heq
    apply hne
    have h : a.1 = a.2 := by
      have := congrArg Prod.fst heq
      simpa using this.symm
    rw [if_neg (by rw [h]; exact G.irrefl)]
  · intro a ha
    simp only [Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at ha ⊢
    exact ⟨ha.2, ha.1⟩
  · intro a _
    exact Prod.swap_swap a

/-- If a vertex `v` of `t` has at least `m` red neighbours in `t` and `R(p, q+1) ≤ m`, then `t`
contains a red `(p+1)`-clique or a blue `(q+1)`-clique. -/
