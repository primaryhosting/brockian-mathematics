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

lemma uesMachine_decides
    (hf : ∀ (n : ℕ) (hn : 0 < n), IsUniversalSeq (f n hn) (bnd C d n)) :
    (uesMachine C d f).Decides USTCON := by
  intro n G s t
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hne : ∀ j, ¬ Reach G s t → walk G (f n hn) s j ≠ t := by
    intro j h hj
    exact h (hj ▸ reach_walk G (f n hn) s j)
  constructor
  · intro hP
    obtain ⟨k, hkL, hkt⟩ := hf n hn G s t hP
    have hex : ∃ m, walk G (f n hn) s m = t := ⟨k, hkt⟩
    have hk0 : walk G (f n hn) s (Nat.find hex) = t := Nat.find_spec hex
    have hk0le : Nat.find hex ≤ bnd C d n := le_trans (Nat.find_min' hex hkt) hkL
    refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [uesMachine_run C d f hn G s t]
      have : min (Nat.find hex) (bnd C d n) = Nat.find hex := by omega
      simp [uesMachine, this, hk0]
    · intro j hj
      rw [uesMachine_run C d f hn G s t]
      have hjL : min j (bnd C d n) = j := by omega
      have hjt : walk G (f n hn) s j ≠ t := Nat.find_min hex hj
      simp [uesMachine, hjL, hjt]
      omega
  · intro hP
    refine ⟨bnd C d n, ?_, ?_⟩
    · rw [uesMachine_run C d f hn G s t]
      simp [uesMachine, hne _ hP]
    · intro j hj
      rw [uesMachine_run C d f hn G s t]
      have hjL : min j (bnd C d n) = j := by omega
      simp [uesMachine, hjL, hne _ hP]
      omega

