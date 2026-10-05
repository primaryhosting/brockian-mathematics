/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Undirected s-t connectivity in logarithmic space (`SL = L`)

This file develops a self-contained formalisation of the statement
"undirected s-t connectivity is decidable in logarithmic space".

## The model of computation

A log-space machine working on `n`-vertex graphs is modelled by
`CS.GraphMachine`: a family of *configuration spaces* `Conf n`, one for each
input size, together with

* an initial configuration `init n s t` (the machine starts knowing the two
  distinguished vertices, which take `O(log n)` bits to write down);
* a *query* function, selecting the single entry of the adjacency matrix that
  the machine inspects in the current configuration (this is the read-only
  input head: the input is never stored in the configuration);
* a deterministic transition `step`, depending only on the current
  configuration and the bit that was read;
* an output function `out`, which is `none` while the machine is still running.

The machine runs in space `O(log n)` exactly when its configuration space has
polynomial size, which is what `CS.GraphMachine.PolySize` records.  This is the
standard configuration-graph characterisation of log-space computation.

`CS.InLogspace P` says that some polynomially-sized machine decides `P`, where
"decides" means that the *first* output produced by the machine is the correct
answer (`CS.GraphMachine.Decides`).

## The result

`CS.reingold_sl_l` shows that undirected s-t connectivity (`CS.USTCON`) is
decided by such a machine, assuming the combinatorial core of Reingold's
theorem, stated here as `CS.UESHypothesis`: for every vertex count `n` there is
a *universal exploration sequence* of polynomial length, i.e. a single sequence
of vertex names `u 0, u 1, …` such that the greedy walk
"move to `u k` if it is adjacent to the current vertex, otherwise stay put"
started anywhere visits the whole connected component of its starting point.

`CS.exists_universal_seq` proves unconditionally that universal exploration
sequences always exist (with no bound on their length), so the content of
`CS.UESHypothesis` is exactly the polynomial length bound, which is the
combinatorial heart of Reingold's theorem.
-/

namespace CS

/-! ## Undirected graphs and connectivity -/

/-- An undirected graph on the vertex set `Fin n`, given by a symmetric
adjacency matrix. -/

def USTCON : ∀ n : ℕ, UGraph n → Fin n → Fin n → Prop := fun _ G s t => Reach G s t

/-! ## Log-space machines on graphs -/

/-- A deterministic machine deciding properties of `n`-vertex undirected
graphs.  The input (the adjacency matrix) is only accessible through the
`query`/`step` interface: in each configuration the machine names one matrix
entry and its transition may depend on the value of that single bit. -/
structure GraphMachine where
  /-- The configuration space for inputs with `n` vertices. -/
  Conf : ℕ → Type
  /-- Configurations form a finite type. -/
  fintypeConf : ∀ n, Fintype (Conf n)
  /-- The initial configuration, given the two distinguished vertices. -/
  init : ∀ n, Fin n → Fin n → Conf n
  /-- The adjacency-matrix entry inspected in the current configuration. -/
  query : ∀ n, Conf n → Fin n × Fin n
  /-- The transition function, reading the queried bit. -/
  step : ∀ n, Conf n → Bool → Conf n
  /-- The output: `none` while the computation is still running. -/
  out : ∀ n, Conf n → Option Bool

attribute [instance] GraphMachine.fintypeConf

/-- The configuration after `k` steps. -/
