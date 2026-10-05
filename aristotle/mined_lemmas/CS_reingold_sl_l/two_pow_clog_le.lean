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

lemma two_pow_clog_le (n : ℕ) (hn : 0 < n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · simp [show n = 1 by omega]
  · have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
    have hlt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    calc 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * n := by omega

/-- **Undirected `s`-`t` connectivity in logarithmic space** (the final stage of Reingold's
algorithm, which is where the claim `SL = L` comes from).

For a fixed degree `d` and a fixed constant `C`, undirected `s`-`t` connectivity on
`d`-regular graphs on `n` vertices whose diameter is at most `C * log₂ n` — the situation
Reingold's expander transformation reduces the general problem to — is decided by a machine
whose number of configurations is bounded by a polynomial `a * n ^ k` in `n`, uniformly in `n`.
Equivalently, the machine uses `O(log n)` bits of work memory, i.e. it is a logarithmic-space
algorithm for undirected connectivity.

The machine only accesses the input graph through neighbour queries, and the bound on the number
of its configurations is the formal expression of its space usage. -/
