/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
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

set_option grind.warning false

/-!
## Scope of this file

Reingold's theorem `SL = L` says that undirected `s`-`t` connectivity can be decided in
logarithmic space.  Its proof has two ingredients:

1. a logarithmic-space transformation turning an arbitrary undirected graph into a
   constant-degree graph of logarithmic diameter (an expander), preserving connectivity, and
2. the observation that connectivity in a constant-degree graph of logarithmic diameter is
   decidable in logarithmic space, by exhaustively trying all label sequences of logarithmic
   length.

What is formalized and proved here, axiom-free, is a complete machine model of space-bounded
computation with oracle access to the input graph, together with step 2: the theorem
`CS.reingold_sl_l` builds an explicit machine with polynomially many configurations (i.e.
`O(log n)` bits of memory) that decides `s`-`t` connectivity on `d`-regular graphs of diameter
at most `C * log₂ n`.  Step 1 — the expander transformation via the zig-zag product — is *not*
formalized here, so the general statement `SL = L` is not obtained.
-/

namespace CS

/-! ## Undirected graphs given by a rotation map -/

/-- A `d`-regular undirected graph on the vertex set `Fin n`, presented (as in Reingold's
algorithm) by a *rotation map*: `nbr v i` is the `i`-th neighbour of `v`, and `rot v i` is the
label under which the edge is traversed backwards.  The axiom `nbr_rot` says that following an
edge and then its reverse label returns to the starting vertex; this is exactly what makes the
adjacency relation symmetric, i.e. the graph undirected. -/
structure LGraph (n d : ℕ) where
  nbr : Fin n → Fin d → Fin n
  rot : Fin n → Fin d → Fin d
  nbr_rot : ∀ v i, nbr (nbr v i) (rot v i) = v

variable {n d : ℕ}

/-- Adjacency of the labelled graph. -/

theorem exists_machine_of_diameter {n d : ℕ} (hd : 0 < d) (D : ℕ) (G : LGraph n d) (s t : Fin n)
    (hD : G.HasDiameterAtMost D) :
    ∃ M : Machine n d, Fintype.card M.State ≤ d ^ D * ((D + 1) * n) ∧ M.Decides G s t := by
  refine ⟨searchMachine hd D s t, le_of_eq (card_searchMachine hd D s t), ?_, ?_⟩
  · intro hreach
    obtain ⟨c, j, hj, hcj⟩ := hD s t hreach
    obtain ⟨k, hk, hdig⟩ := exists_code hd D c
    have hW : Wk G hd s k j = t := by
      have : Wk G hd s k j = G.walk s c j := by
        refine walk_congr G s _ c j ?_
        intro i hi
        exact Fin.ext (hdig i (by omega))
      rw [this, hcj]
    obtain ⟨m, hm⟩ :=
      halts_true (G := G) hd (d ^ D - 0) 0 (pow_pos hd D) rfl ⟨k, j, Nat.zero_le k, hk, hj, hW⟩
    exact ⟨m, hm⟩
  · intro hreach
    obtain ⟨m, hm⟩ := halts_false (G := G) (s := s) (t := t) hd (d ^ D - 0) 0 (pow_pos hd D) rfl
      (by
        intro k' j _ _ _ hW
        exact hreach (hW ▸ reach_Wk G hd s k' j))
    exact ⟨m, hm⟩


/-! ## Logarithmic space

`Fintype.card M.State ≤ a * n ^ k` says exactly that the machine's memory consists of
`O(log n)` bits, i.e. that it runs in logarithmic space. -/

