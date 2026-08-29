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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Reachability in a finite directed graph

We work with a directed graph on the vertex set `{0, 1, ..., n-1}` given by a Boolean
adjacency function `g`.  `reachB n g s i v` says that `v` is reachable from `s` by a walk of
length *at most* `i` (we allow "staying put" at each step, so walks of length exactly `i`
with lazy steps are the same thing as walks of length at most `i`). -/

section Graph

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s : ℕ)

/-- `reachB n g s i v = true` iff `v` is reachable from `s` in at most `i` steps
(inside the vertex set `{0,…,n-1}`). -/

lemma mem_Box_of_Inv (hs : s < n) (ht : t < n) {w : St} (h : Inv n g s t w) :
    w ∈ Box (n + 2) := by
  cases w with
  | levelStart i c =>
      obtain ⟨hi, hc⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      exact mem_Box (m := n + 2) (tag := 0) (x := (i, c, 0, 0, 0, 0, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | outer i c d j =>
      obtain ⟨hi, hc, hj, hd⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hdn : d ≤ n := by rw [hd]; exact le_trans (cntUpto_le _ _) hj
      exact mem_Box (m := n + 2) (tag := 1) (x := (i, c, d, j, 0, 0, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | walkYes i c d j w r =>
      obtain ⟨hi, hc, hj, hd, hr, hrw⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hdn : d ≤ n := by rw [hd]; exact le_trans (cntUpto_le _ _) (le_of_lt hj)
      have hwn : w < n := reachB_lt hs hrw
      exact mem_Box (m := n + 2) (tag := 2) (x := (i, c, d, j, w, r, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | inner i c d j u e =>
      obtain ⟨hi, hc, hu, he, h1, h2, hdn⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hen : e ≤ n := le_trans he (le_trans (cntPhi_le _ _ _) hu)
      have hjn : j < n := by
        rcases Nat.lt_or_ge i n with hlt | hge
        · exact (h1 hlt).1
        · have : i = n := by omega
          rw [h2 this]; exact ht
      exact mem_Box (m := n + 2) (tag := 3) (x := (i, c, d, j, u, e, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | walkIn i c d j u e w r =>
      obtain ⟨hi, hc, hu, he, h1, h2, hr, hrw, hdn⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hen : e ≤ n := le_trans he (le_trans (cntPhi_le _ _ _) (le_of_lt hu))
      have hwn : w < n := reachB_lt hs hrw
      have hjn : j < n := by
        rcases Nat.lt_or_ge i n with hlt | hge
        · exact (h1 hlt).1
        · have : i = n := by omega
          rw [h2 this]; exact ht
      exact mem_Box (m := n + 2) (tag := 4) (x := (i, c, d, j, u, e, w, r)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | acc =>
      exact mem_Box (m := n + 2) (tag := 5) (x := (0, 0, 0, 0, 0, 0, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))

end Bound

/-! ## The Immerman-Szelepcsenyi theorem: `NL = coNL` -/

/-- **Immerman-Szelepcsenyi theorem** (`NL = coNL`).

Let `g` be (the adjacency function of) a directed graph on the vertex set `{0, …, n-1}` — for
instance the configuration graph of a nondeterministic space-bounded machine — and let `s`, `t`
be two vertices.  The nondeterministic machine `Step n g s t` (the inductive counting machine of
Immerman and Szelepcsenyi, whose transitions are local: each of them compares numbers `< n + 2`
and performs at most one query to `g`) satisfies:

1. it accepts, i.e. it has a run from the initial configuration to the accepting configuration,
   if and only if `t` is **not** reachable from `s` in the graph;
2. every configuration reachable from the initial one lies in the explicit set `Box (n + 2)`,
   whose cardinality is at most `6 * (n + 2) ^ 8`, i.e. the machine only uses `O(log n)` bits of
   workspace.

Applied to the configuration graph of a nondeterministic machine running in space `S(m) ≥ log m`
(which has `n = 2 ^ O(S(m))` configurations), this says that the complement of its language is
accepted by a nondeterministic machine that runs in space `O(S(m))`: nondeterministic space is
closed under complementation, `NL = coNL`. -/
