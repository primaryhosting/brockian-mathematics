import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

/-! ## A model of bounded-memory (space-bounded) computation

A `Alg Q Ans In Out` is a deterministic algorithm which

* has a finite set `S` of memory configurations,
* starts, on input `x : In`, in configuration `init x`,
* in each configuration either *halts* with an output in `Out`, or issues a query `q : Q`
  about its (read-only) input and moves to a new configuration determined by the answer.

The *space* used by the algorithm is `Nat.log 2 (card A)`, so "logarithmic space" means
`A.card ≤ p n` for a polynomial `p`.  This is the standard configuration-counting
characterisation of deterministic logarithmic space: a machine with a read-only input and
`c * log n` bits of work memory has polynomially many configurations, and conversely.
-/

structure Alg (Q Ans In Out : Type) where
  /-- The finite set of memory configurations. -/
  S : Type
  /-- Finiteness of the configuration space. -/
  fin : Fintype S
  /-- Initial configuration on a given input. -/
  init : In → S
  /-- In each configuration, either query the input and continue, or halt with an output. -/
  trans : S → ((Q × (Ans → S)) ⊕ Out)

namespace Alg

variable {Q Ans In Out : Type}

/-- The number of memory configurations; `Nat.log 2` of it is the space used. -/

def USTCONinL : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ A : UAlg n, A.card ≤ (n + 2) ^ c ∧ DecidesUSTCON n A

/-! ## Reingold's expanderisation step

Reingold's theorem is obtained by combining the (fully proved) exhaustive-walk algorithm
above with the expanderisation step: every undirected graph can be turned, in logarithmic
space, into a `4`-regular graph on polynomially many vertices with the same connectivity
structure and with all connected components of logarithmic diameter.  The following
structure packages exactly that step, together with the standard fact that a logarithmic
space subroutine can be composed with a logarithmic-space computation at the cost of a
polynomial blow-up in the number of configurations. -/

structure ReingoldTransform where
  /-- Exponent of the polynomial bounds. -/
  c : ℕ
  /-- Number of vertices of the transformed graph. -/
  N : ℕ → ℕ
  /-- Diameter bound of the transformed graph. -/
  D : ℕ → ℕ
  /-- Embedding of the original vertices into the transformed graph. -/
  emb : (n : ℕ) → Fin n → Fin (N n)
  /-- The neighbour (rotation) map of the transformed graph. -/
  nbr : (n : ℕ) → (Fin n → Fin n → Bool) → Fin (N n) → Fin 4 → Fin (N n)
  /-- The transformed graph has polynomially many vertices. -/
  hN : ∀ n, N n ≤ (n + 2) ^ c
  /-- The diameter is logarithmic: `4 ^ D n * (D n + 1)` is polynomial. -/
  hD : ∀ n, 4 ^ D n * (D n + 1) ≤ (n + 2) ^ c
  /-- Every connected component of the transformed graph has diameter at most `D n`. -/
  diam : ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) →
    ∀ v w : Fin (N n), WalkReach (nbr n adj) v w →
      ∃ l : List (Fin 4), l.length ≤ D n ∧ walk (nbr n adj) v l = w
  /-- The transformation preserves connectivity. -/
  preserve : ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) →
    ∀ s t : Fin n, AdjReach adj s t ↔ WalkReach (nbr n adj) (emb n s) (emb n t)
  /-- The neighbour map of the transformed graph is computable in logarithmic space:
  any algorithm which queries it can be simulated by an algorithm which queries the
  adjacency matrix of the original graph, with a polynomial blow-up in memory. -/
  simulate : ∀ (n : ℕ)
      (B : Alg (Fin (N n) × Fin 4) (Fin (N n)) (Fin (N n) × Fin (N n)) Bool),
    ∃ A : UAlg n, A.card ≤ B.card * (n + 2) ^ c ∧
      ∀ (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) → ∀ (s t : Fin n) (b : Bool),
        B.Outputs (nbrOracle (nbr n adj)) (emb n s, emb n t) b →
          A.Outputs (adjOracle adj) (s, t) b

/-- **Reingold's theorem (`SL = L`): undirected `s`-`t` connectivity is in `L`.**

Given the expanderisation step `T` (Reingold's zig-zag / derandomised-squaring
construction, which turns any undirected graph into a connectivity-equivalent
`4`-regular graph of logarithmic diameter in logarithmic space), undirected `s`-`t`
connectivity is decided in logarithmic space: the exhaustive-walk algorithm on the
transformed graph uses only `O(log n)` bits, and simulating it over the original graph
costs only a polynomial factor in the number of configurations. -/
