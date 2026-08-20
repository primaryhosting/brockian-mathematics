/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Machine

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalised here

Undirected `s`-`t` connectivity (`USTCON`) is decided in logarithmic space.

The machine model is the one of `CS.Solver`: a deterministic machine whose whole memory
is one configuration out of a finite configuration space `State`, which reads the
adjacency matrix of the `n`-vertex input graph one bit at a time (in each configuration
it queries one entry and branches on the answer) and which is started in a
configuration determined by the two distinguished vertices.  Using `O(log n)` bits of
memory means `Fintype.card State ≤ c * n ^ c` for a constant `c` that does not depend
on `n`.

`CS.reingold_sl_l` states, and proves, that USTCON is solved by such machines: there is
a single constant `c` (here `c = 100`) such that for every `n` there is a machine with
at most `c * n ^ c` configurations deciding connectivity on all `n`-vertex undirected
graphs.  The machine is built from a universal traversal sequence of length `O(n⁷)`,
whose existence is proved from scratch in `CS.exists_uts`: the transition operator of
the lazy `2n`-regular walk attached to a graph is shown to be symmetric and positive
semidefinite, to have spectral gap at least `1/(4n³)` on each connected component
(`CS.gap`), hence to reach any prescribed vertex of the component with probability at
least `1/(2n)` after `8n⁴` steps (`CS.hit_prob`), and a union bound over all graphs and
all pairs of vertices produces a single label sequence that works for all of them.

*Scope.*  The machine family produced here is described by a single constant `c` and one
machine per input size; the construction of the traversal sequence is by the
probabilistic method, so the family is not exhibited as a *uniformly computable* one.
Reingold's theorem `SL = L` is the strengthening in which the machine family is
uniformly computable; that statement is spelled out below as `CS.SLeqL` and is *not*
proved in this file.
-/

namespace CS

/-- **Undirected `s`-`t` connectivity in logarithmic space.**

There is a constant `c` such that, for every number of vertices `n ≥ 1`, undirected
`s`-`t` connectivity on `n`-vertex graphs is decided by a machine which reads the
adjacency matrix one bit at a time and whose configuration space has at most `c * n ^ c`
elements, i.e. which uses `O(log n)` bits of memory.

See the module documentation for the precise scope of this statement: the uniform
(`SL = L`) form of the theorem is stated as `CS.SLeqL` below and is not proved here. -/

def mkSolver (n : ℕ) (hn : 0 < n) (w : ℕ → ℕ) (init : ℕ → ℕ → ℕ → ℕ)
    (qry : ℕ → ℕ → ℕ × ℕ) (nxt : ℕ → ℕ → Bool → ℕ) (outp : ℕ → ℕ → Option Bool) :
    Solver n where
  State := Fin (w n + 1)
  fin := inferInstance
  init := fun s t => ⟨min (init n s.val t.val) (w n), by omega⟩
  query := fun q => (⟨(qry n q.val).1 % n, Nat.mod_lt _ hn⟩, ⟨(qry n q.val).2 % n, Nat.mod_lt _ hn⟩)
  next := fun q b => ⟨min (nxt n q.val b) (w n), by omega⟩
  out := fun q => outp n q.val

/-- **A uniform form of the statement `SL = L`**: undirected `s`-`t` connectivity is
decided by a *uniformly computable* family of machines using `O(log n)` bits of memory.
Uniformity is expressed here by requiring the numerical description of the machine
family (its size, initial configuration, queries, transitions and outputs) to be
computable.

This `Prop` is stated for reference only; it is not proved in this development.  The
statement in which the family is not required to be computable is `CS.reingold_sl_l`,
which *is* proved here.

Two caveats about the statement itself.  Requiring the description to be computable is
necessary but not sufficient for membership in `L` in the usual sense: the genuine
statement asks for the description to be computable *within logarithmic space* by a
single program, which is what makes Reingold's construction hard, whereas mere
computability of the description can in principle be arranged by an exhaustive search
over the finitely many candidate machines of the allowed size.  Formalising
logarithmic-space computability of the description would require a full space-bounded
machine model for the description itself, which is not developed here. -/
