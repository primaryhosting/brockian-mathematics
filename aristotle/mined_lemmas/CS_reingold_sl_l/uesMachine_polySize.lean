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

lemma uesMachine_polySize : (uesMachine C d f).PolySize := by
  refine ⟨C + 1, d + 2, fun n => ?_⟩
  have : Fintype.card ((uesMachine C d f).Conf n) = n * (n * (bnd C d n + 1)) := by
    simp [uesMachine, Fintype.card_prod]
  rw [this]
  have h1 : n * (n * (bnd C d n + 1)) ≤ (n + 1) * ((n + 1) * (C * (n + 1) ^ d + 1)) := by
    have : bnd C d n = C * (n + 1) ^ d := rfl
    rw [this]
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) le_rfl)
  refine h1.trans ?_
  have h2 : (n + 1) * ((n + 1) * (C * (n + 1) ^ d + 1)) = (n + 1) ^ 2 * (C * (n + 1) ^ d + 1) := by
    ring
  rw [h2]
  have h3 : C * (n + 1) ^ d + 1 ≤ (C + 1) * (n + 1) ^ d := by
    have : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith [Nat.one_le_pow d (n + 1) (by omega : 0 < n + 1)]
  calc (n + 1) ^ 2 * (C * (n + 1) ^ d + 1) ≤ (n + 1) ^ 2 * ((C + 1) * (n + 1) ^ d) :=
        Nat.mul_le_mul_left _ h3
    _ = (C + 1) * (n + 1) ^ (d + 2) := by ring

