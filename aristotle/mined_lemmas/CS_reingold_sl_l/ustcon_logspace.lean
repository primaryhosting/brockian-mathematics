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

theorem ustcon_logspace :
    ∃ c : ℕ, ∀ n : ℕ, 0 < n → ∃ M : Solver n,
      Fintype.card M.State ≤ c * n ^ c ∧ M.Correct := by
  refine ⟨100, fun n hn => ?_⟩
  obtain ⟨σ, hlen, hσ⟩ := exists_uts (n := n) hn
  refine ⟨utsSolver σ, ?_, utsSolver_correct hσ⟩
  have hL : σ.length ≤ 64 * n ^ 7 := hlen ▸ utsLen_le hn
  have hcard := utsSolver_card σ
  have h1 : 1 ≤ n := hn
  calc Fintype.card (utsSolver σ).State = 2 * n + n * (n * (σ.length + 1)) := hcard
    _ ≤ 2 * n + n * (n * (64 * n ^ 7 + 1)) := by
        have := Nat.add_le_add_right hL 1
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)) _
    _ ≤ 100 * n ^ 100 := by
        have hpow : n ^ 9 ≤ n ^ 100 := Nat.pow_le_pow_right h1 (by norm_num)
        have hn2 : n ≤ n ^ 9 := Nat.le_self_pow (by norm_num) n
        have hn3 : n * n ≤ n ^ 9 := by
          calc n * n = n ^ 2 := by ring
            _ ≤ n ^ 9 := Nat.pow_le_pow_right h1 (by norm_num)
        have hn4 : n * (n * (64 * n ^ 7)) = 64 * n ^ 9 := by ring
        nlinarith [hpow, hn2, hn3]

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Setup

/-!
Elementary properties of the rotation map, of connectivity and of label sequences.
-/

namespace CS

open Finset

variable {n : ℕ} {A : Fin n → Fin n → Bool}

