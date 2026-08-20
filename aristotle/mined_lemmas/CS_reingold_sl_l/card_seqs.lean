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

lemma card_seqs (m : ℕ) : (seqs n m).card = (2 * n) ^ m := by
  induction m with
  | zero => simp [seqs]
  | succ m ih =>
      have hdisj : ∀ a ∈ (univ : Finset (Lab n)), ∀ b ∈ (univ : Finset (Lab n)), a ≠ b →
          Disjoint ((seqs n m).image (a :: ·)) ((seqs n m).image (b :: ·)) := by
        intro a _ b _ hab
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro σ ⟨τ, -, rfl⟩ ⟨τ', -, h⟩
        exact hab (by simpa using (List.cons.injEq _ _ _ _ ▸ h).1.symm)
      have : (seqs n (m + 1)).card
          = ∑ _a : Lab n, ((seqs n m).image (fun τ => _a :: τ)).card := by
        simp only [seqs]
        exact Finset.card_biUnion hdisj
      rw [this]
      have himg : ∀ a : Lab n, ((seqs n m).image (fun τ => a :: τ)).card = (seqs n m).card := by
        intro a
        apply Finset.card_image_of_injective
        intro x y hxy
        simpa using hxy
      simp only [himg, ih, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      have : Fintype.card (Lab n) = 2 * n := by simp [Lab]
      rw [this]
      ring

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Hitting

/-!
Existence of polynomially long universal traversal sequences, by the probabilistic
method: block by block, the walk fails to reach a prescribed vertex of its component
with probability at most `1 - 1/(2n)`, and a union bound over all symmetric graphs and
all pairs of vertices leaves a sequence that works for all of them.
-/

namespace CS

open Finset

open scoped Classical

variable {n : ℕ} {A : Fin n → Fin n → Bool}

/-- Length of one block of the traversal sequence. -/
