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

lemma exists_walk_lt (G : LGraph n d) (s v : Fin n) :
    ∀ (j : ℕ) (c : ℕ → Fin d), G.walk s c j = v → ∃ (c' : ℕ → Fin d) (j' : ℕ),
      j' < n ∧ G.walk s c' j' = v := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro c hc
    rcases Nat.lt_or_ge j n with hj | hj
    · exact ⟨c, j, hj, hc⟩
    · have hcard : Fintype.card (Fin n) < Fintype.card (Fin (j + 1)) := by
        simp only [Fintype.card_fin]; omega
      obtain ⟨x, y, hxy, hfxy⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (j + 1) => G.walk s c (i : ℕ)) hcard
      -- put the two coinciding positions in increasing order
      obtain ⟨a, b, hab, hb, heq⟩ :
          ∃ a b : ℕ, a < b ∧ b ≤ j ∧ G.walk s c a = G.walk s c b := by
        rcases lt_or_gt_of_ne (fun h : (x : ℕ) = (y : ℕ) => hxy (Fin.ext h)) with h | h
        · exact ⟨(x : ℕ), (y : ℕ), h, Nat.lt_succ_iff.mp y.isLt, hfxy⟩
        · exact ⟨(y : ℕ), (x : ℕ), h, Nat.lt_succ_iff.mp x.isLt, hfxy.symm⟩
      set sh := b - a with hsh
      set c' : ℕ → Fin d := fun m => if m < a then c m else c (m + sh) with hc'
      have hstart : G.walk s c' a = G.walk s c b := by
        rw [walk_congr G s c' c a (fun m hm => by simp [hc', hm]), heq]
      have hrun : ∀ m, G.walk s c' (a + m) = G.walk s c (b + m) := by
        intro m
        induction m with
        | zero => simpa using hstart
        | succ m ihm =>
            show G.nbr (G.walk s c' (a + m)) (c' (a + m)) = _
            rw [ihm]
            have : c' (a + m) = c (b + m) := by
              simp only [hc', if_neg (by omega : ¬ a + m < a), hsh]
              congr 1
              omega
            rw [this]
            rfl
      have hfinal : G.walk s c' (j - sh) = v := by
        have h1 : j - sh = a + (j - b) := by omega
        have h2 : b + (j - b) = j := by omega
        rw [h1, hrun (j - b), h2, hc]
      exact ih (j - sh) (by omega) c' hfinal

/-- Every `d`-regular graph on `n` vertices has diameter at most `n - 1`. -/
