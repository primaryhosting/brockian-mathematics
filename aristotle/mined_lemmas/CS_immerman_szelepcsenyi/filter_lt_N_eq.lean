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

/-
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/

theorem filter_lt_N_eq (hs : s < N) (i : ℕ) :
    (R N adj s i).filter (fun x => x < N) = R N adj s i := by
  apply Finset.filter_true_of_mem
  intro x hx
  simpa using R_subset_range hs i hx

/-!
## The complement machine

We now describe, for a digraph `(N, adj)` with distinguished vertices `s` and `t`, a
nondeterministic machine whose configuration graph is *polynomially* larger than the digraph
itself, and which has an accepting run exactly when `t` is **not** reachable from `s`.

This is the inductive-counting construction of Immerman and Szelepcsényi.  Reading the digraph
as the configuration graph of a nondeterministic machine of space `S` (so `N = 2^{O(S)}`),
the new machine has `O(N^8)` configurations, i.e. it also runs in space `O(S)`.
-/

/-- Configurations of the complement machine.

* `outer i c v k`   : round `i`; `c = |R (i-1)|`; deciding vertex `v`; `k` vertices `< v` are in `R i`.
* `pathA i c v k p l` : verifying `v ∈ R i` by guessing a walk `s → … → p` of length `l ≤ i`.
* `inner i c v k d lb` : verifying `v ∉ R i` by enumerating `R (i-1)`; `d` elements listed so far,
  all of them `< lb`.
* `pathB i c v k d u p l` : verifying `u ∈ R (i-1)` by guessing a walk `s → … → p` of length `l`.
* `acc` : the accepting configuration. -/
inductive Cfg where
  | outer (i c v k : ℕ) : Cfg
  | pathA (i c v k p l : ℕ) : Cfg
  | inner (i c v k d lb : ℕ) : Cfg
  | pathB (i c v k d u p l : ℕ) : Cfg
  | acc : Cfg
  deriving DecidableEq, Repr

/-- The (nondeterministic) transition relation of the complement machine.  Every transition
inspects at most one entry of the adjacency matrix. -/
inductive Step (N : ℕ) (adj : ℕ → ℕ → Bool) (s t : ℕ) : Cfg → Cfg → Prop
  /-- Guess that `v ∈ R i`, and start verifying it. -/
  | startA {i c v k : ℕ} : v < N → Step N adj s t (.outer i c v k) (.pathA i c v k s 0)
  /-- Extend the guessed walk. -/
  | stepA {i c v k p p' l : ℕ} : adj p p' = true → p' < N → l + 1 ≤ i →
      Step N adj s t (.pathA i c v k p l) (.pathA i c v k p' (l + 1))
  /-- The walk arrived at `v`; record `v ∈ R i` and move on. -/
  | doneA {i c v k p l : ℕ} : p = v →
      Step N adj s t (.pathA i c v k p l) (.outer i c (v + 1) (k + 1))
  /-- Guess that `v ∉ R i`, and start enumerating `R (i-1)`. -/
  | startI {i c v k : ℕ} : v < N → Step N adj s t (.outer i c v k) (.inner i c v k 0 0)
  /-- Guess the next element `u` of `R (i-1)`, and start verifying `u ∈ R (i-1)`. -/
  | startB {i c v k d lb u : ℕ} : d < c → lb ≤ u → u < N →
      Step N adj s t (.inner i c v k d lb) (.pathB i c v k d u s 0)
  /-- Extend the guessed walk. -/
  | stepB {i c v k d u p p' l : ℕ} : adj p p' = true → p' < N → l + 1 ≤ i - 1 →
      Step N adj s t (.pathB i c v k d u p l) (.pathB i c v k d u p' (l + 1))
  /-- The walk arrived at `u`; check that `u` is not `v` and has no edge to `v`. -/
  | doneB {i c v k d u p l : ℕ} : p = u → u ≠ v → adj u v = false →
      Step N adj s t (.pathB i c v k d u p l) (.inner i c v k (d + 1) (u + 1))
  /-- All of `R (i-1)` has been enumerated, so `v ∉ R i`; move on to the next vertex. -/
  | doneI {i c v k d lb : ℕ} : d = c → i ≤ N →
      Step N adj s t (.inner i c v k d lb) (.outer i c (v + 1) k)
  /-- Round `i` is finished: `k = |R i|` becomes the count for the next round. -/
  | nextRound {i c k : ℕ} : i < N → Step N adj s t (.outer i c N k) (.outer (i + 1) k 0 0)
  /-- The last round is finished; check `t ∉ R (N+1)`. -/
  | lastRound {c k : ℕ} : Step N adj s t (.outer N c N k) (.inner (N + 1) k t 0 0 0)
  /-- All of `R N` has been enumerated and avoided `t`, so `t` is unreachable. -/
  | accept {c k d lb : ℕ} : d = c → Step N adj s t (.inner (N + 1) c t k d lb) .acc

/-- The initial configuration: round `1`, with `|R 0| = 1`. -/
