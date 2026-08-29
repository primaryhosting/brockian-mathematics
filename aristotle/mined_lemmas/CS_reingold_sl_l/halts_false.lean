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

lemma halts_false {D : ℕ} (hd : 0 < d) {s t : Fin n} :
    ∀ (r k : ℕ) (hk : k < d ^ D), d ^ D - k = r →
      (∀ k' j, k ≤ k' → k' < d ^ D → j ≤ D → Wk G hd s k' j ≠ t) →
      ∃ m, (searchMachine hd D s t).multi G m (stq k 0 hk (Nat.zero_le D) s) = Sum.inr false := by
  intro r
  induction r with
  | zero => intro k hk hr _; omega
  | succ r ih =>
      intro k hk hr hno'
      have hno : ∀ j, j ≤ D → Wk G hd s k j ≠ t := fun j hj => hno' k j le_rfl hk hj
      obtain ⟨m1, hm1⟩ := sweep_to_end (t := t) hd k hk hno 0 (Nat.zero_le D)
      have hm1' : (searchMachine hd D s t).multi G m1 (stq k 0 hk (Nat.zero_le D) s)
          = Sum.inl (stq k D hk le_rfl (Wk G hd s k D)) := hm1
      by_cases hlast : k + 1 = d ^ D
      · refine ⟨m1 + 1, ?_⟩
        rw [Machine.multi_add hm1',
          Machine.multi_succ_inr (stepS_last (G := G) hd hk (hno D le_rfl) hlast)]
      · have hk1 : k + 1 < d ^ D := by omega
        obtain ⟨m2, hm2⟩ := ih (k + 1) hk1 (by omega)
          fun k'' j hk'' h1 h2 => hno' k'' j (by omega) h1 h2
        refine ⟨m1 + (m2 + 1), ?_⟩
        rw [Machine.multi_add hm1',
          Machine.multi_succ_inl (stepS_advance (G := G) hd hk (hno D le_rfl) hk1)]
        exact hm2

/-- Every sequence of `D` labels is the base-`d` expansion of some `k < d ^ D`. -/
