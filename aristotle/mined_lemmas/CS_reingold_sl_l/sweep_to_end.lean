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

lemma sweep_to_end {D : ℕ} (hd : 0 < d) {s t : Fin n} (k : ℕ) (hk : k < d ^ D)
    (hno : ∀ j, j ≤ D → Wk G hd s k j ≠ t) :
    ∀ (i : ℕ) (hi : i ≤ D), ∃ m,
      (searchMachine hd D s t).multi G m (stq k i hk hi (Wk G hd s k i))
        = Sum.inl (stq k D hk le_rfl (Wk G hd s k D)) := by
  have key : ∀ (p i : ℕ) (hi : i ≤ D), D - i = p → ∃ m,
      (searchMachine hd D s t).multi G m (stq k i hk hi (Wk G hd s k i))
        = Sum.inl (stq k D hk le_rfl (Wk G hd s k D)) := by
    intro p
    induction p with
    | zero =>
        intro i hi hp
        have : i = D := by omega
        subst this
        exact ⟨0, rfl⟩
    | succ p ih =>
        intro i hi hp
        have hiD : i < D := by omega
        obtain ⟨m, hm⟩ := ih (i + 1) hiD (by omega)
        exact ⟨m + 1, by
          rw [Machine.multi_succ_inl (stepS_step (G := G) hd hk hiD (hno i hi))]
          exact hm⟩
  intro i hi
  exact key (D - i) i hi rfl

/-- If `t` occurs somewhere on a walk with index at least `k`, the machine started at sequence
`k` halts with `true`. -/
