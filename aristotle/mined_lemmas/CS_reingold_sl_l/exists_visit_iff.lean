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

theorem exists_visit_iff {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s t : Fin n) :
    (∃ k, k ≤ Tm d D ∧ vAt G D hd s k = t) ↔
      ∃ l : List (Fin d), l.length ≤ D ∧ G.walk s l = t := by
  constructor
  · rintro ⟨k, _, hk⟩
    refine ⟨digitsList hd (k / (D + 1)) (k % (D + 1)), ?_, ?_⟩
    · rw [digitsList_length]
      have hlt : k % (D + 1) < D + 1 := Nat.mod_lt _ (Nat.succ_pos D)
      omega
    · rw [← RotGraph.cwalk_eq_walk G hd s (k / (D + 1)) (k % (D + 1))]
      exact hk
  · rintro ⟨l, hlen, hl⟩
    refine ⟨l.length + (D + 1) * encode l, ?_, ?_⟩
    · have h1 : encode l < d ^ l.length := encode_lt hd l
      have h2 : d ^ l.length ≤ d ^ D := Nat.pow_le_pow_right hd hlen
      have h3 : (D + 1) * (encode l + 1) ≤ (D + 1) * d ^ D :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (D + 1) * (encode l + 1) = (D + 1) * encode l + (D + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      have h5 : (D + 1) * d ^ D = Tm d D := Nat.mul_comm _ _
      omega
    · have hm : 0 < D + 1 := Nat.succ_pos D
      have hmod : (l.length + (D + 1) * encode l) % (D + 1) = l.length := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hdiv : (l.length + (D + 1) * encode l) / (D + 1) = encode l := by
        rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (by omega), Nat.zero_add]
      show G.cwalk hd s ((l.length + (D + 1) * encode l) / (D + 1))
          ((l.length + (D + 1) * encode l) % (D + 1)) = t
      rw [hmod, hdiv, RotGraph.cwalk_eq_walk G hd s (encode l) l.length,
        digitsList_encode hd l]
      exact hl

/-!
## Main theorem

`CS.reingold_sl_l` below is a formalised statement that undirected `s`-`t` connectivity is
solvable in logarithmic space, in the following precise sense.

For a `d`-regular undirected graph on `n` vertices presented by a rotation map, all of
whose connected components have diameter at most `D`, there is a deterministic machine
which reads the graph only through its rotation map (one query per step), uses a memory
with only `2·n³·(d^D·(D+1)+1)` configurations, and decides connectivity of every pair
`s`, `t`.  When `d` is a constant and `D = O(log n)` — exactly the situation Reingold's
zig-zag transformation produces — the number of memory configurations is polynomial in
`n`, i.e. the machine works in space `O(log n)`, so undirected connectivity is in `L`.

This formalises the final phase of Reingold's algorithm: the deterministic
logarithmic-space enumeration of all short label sequences.  The preprocessing phase of
Reingold's proof, which turns an arbitrary undirected graph into a constant-degree graph
of logarithmic diameter by iterated zig-zag products, is *not* formalised here; the
bounded-diameter hypothesis `hdiam` below is what that phase supplies.
-/
