/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/

theorem adj_symm {n d : Nat} (G : RotGraph n d) {u v : Fin n} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(G.rot (u, a)).2, ?_⟩
  have h2 := G.rot_involutive (u, a)
  have h3 : (v, (G.rot (u, a)).2) = G.rot (u, a) := by
    rw [← ha]; rfl
  show (G.rot (v, (G.rot (u, a)).2)).1 = u
  rw [h3, h2]

/-- The endpoint of the walk starting at `v` and following the edge labels in `l`. -/
