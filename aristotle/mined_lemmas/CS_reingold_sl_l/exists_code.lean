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

lemma exists_code {d : ℕ} (hd : 0 < d) (D : ℕ) (c : ℕ → Fin d) :
    ∃ k, k < d ^ D ∧ ∀ i, i < D → dg d k i = (c i : ℕ) := by
  induction D generalizing c with
  | zero => exact ⟨0, by simp, by omega⟩
  | succ D ih =>
      obtain ⟨k', hk', hdig⟩ := ih (fun i => c (i + 1))
      have h0 : (c 0 : ℕ) < d := (c 0).isLt
      have hdiv : ((c 0 : ℕ) + d * k') / d = k' := by
        rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h0, Nat.zero_add]
      refine ⟨(c 0 : ℕ) + d * k', ?_, ?_⟩
      · have hle : d * k' + d ≤ d * d ^ D := by
          have h1 : k' + 1 ≤ d ^ D := hk'
          calc d * k' + d = d * (k' + 1) := by ring
            _ ≤ d * d ^ D := Nat.mul_le_mul_left d h1
        have : d ^ (D + 1) = d * d ^ D := by ring
        omega
      · intro i hi
        match i with
        | 0 =>
            simp only [dg, pow_zero, Nat.div_one]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
        | (i + 1) =>
            have hstep : dg d ((c 0 : ℕ) + d * k') (i + 1) = dg d k' i := by
              unfold dg
              rw [show d ^ (i + 1) = d * d ^ i by ring, ← Nat.div_div_eq_div_mul, hdiv]
            rw [hstep]
            exact hdig i (by omega)

