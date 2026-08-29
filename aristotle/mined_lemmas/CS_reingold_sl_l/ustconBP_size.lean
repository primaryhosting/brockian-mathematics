/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

theorem ustconBP_size [NeZero D] (s t : Fin n) :
    (ustconBP n D k s t).size = D ^ k * k * (n * 2) := by
  simp [BP.size, ustconBP, Fintype.card_prod]

/-! ## The main statement -/

/--
**Reingold's theorem, scoped formalization.**

Reingold's theorem (`SL = L`) says that undirected `s`-`t` connectivity is decidable in
logarithmic space.  Its proof has two halves: a logspace graph transformation (based on the
zig-zag product) turning an arbitrary undirected graph into a constant-degree graph whose
connected components have logarithmic diameter, and then the observation that on such
graphs connectivity is decidable in logarithmic space by exhaustively enumerating all short
walks.  It is that second half which is formalized here, unconditionally, in the standard
non-uniform model of logarithmic space (branching programs of polynomial size, `size = 2 ^
space`).

Precisely: for all constants `c` and `d` there are constants `C`, `p` such that for every
`n` and all vertices `s t` of an `n`-vertex graph there is a branching program of size at
most `C * (n + 1) ^ p` (i.e. using `O(log n)` bits of memory) which reads the graph only
through its neighbour map, and which decides whether `s` and `t` are connected, for every
undirected `2 ^ d`-regular graph all of whose connected components have diameter at most
`c * (log₂ n + 1)`.

The hypothesis on `nbr` expresses that the graph is undirected: every edge can be traversed
backwards.  Connectivity is stated as `SimpleGraph.Reachable` in the underlying simple
graph `ofNbr nbr`, i.e. as ordinary undirected connectivity.
-/
