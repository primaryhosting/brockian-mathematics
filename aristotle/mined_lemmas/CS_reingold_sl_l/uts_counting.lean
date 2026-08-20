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

lemma uts_counting (hn : 0 < n) :
    2 ^ (n * n) * n * n *
        ((2 * n) ^ blockLen n - (2 * n) ^ (blockLen n - 1)) ^ numBlocks n
      < (2 * n) ^ utsLen n := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0:ℝ) < 2 * n := by linarith
  set T : ℕ := blockLen n with hTdef
  set k : ℕ := numBlocks n with hkdef
  have hT1 : 1 ≤ T := by
    rw [hTdef, blockLen]
    have : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
    omega
  have hNle : ((2 * n) ^ (T - 1) : ℕ) ≤ (2 * n) ^ T :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hbase : (0:ℝ) ≤ 1 - 1 / (2 * (n:ℝ)) := by
    have : 1 / (2 * (n:ℝ)) ≤ 1 := by
      rw [div_le_one hNpos]; linarith
    linarith
  -- the scalar estimate
  have hkey : ((2:ℝ) ^ (n * n) * n * n) * (1 - 1 / (2 * (n:ℝ))) ^ k < 1 := by
    have hk : k = (2 * n) * (n + 1) ^ 2 := by rw [hkdef, numBlocks]
    have hhalf : (1 - 1 / (2 * (n:ℝ))) ^ k ≤ (1 / 2) ^ ((n + 1) ^ 2) := by
      rw [hk, pow_mul]
      exact pow_le_pow_left₀ (by positivity) (half_pow_bound hn) _
    have hnlt : (n : ℝ) < 2 ^ n := by
      have : n < 2 ^ n := Nat.lt_two_pow_self
      exact_mod_cast this
    have hnn : (n:ℝ) * n < 2 ^ n * 2 ^ n := by
      have h0 : (0:ℝ) < n := by linarith
      nlinarith
    have hcount : (2:ℝ) ^ (n * n) * n * n < 2 ^ ((n + 1) ^ 2) := by
      have hp1 : (0:ℝ) < 2 ^ (n * n) := by positivity
      calc (2:ℝ) ^ (n * n) * n * n = 2 ^ (n * n) * ((n:ℝ) * n) := by ring
        _ < 2 ^ (n * n) * (2 ^ n * 2 ^ n) := mul_lt_mul_of_pos_left hnn hp1
        _ = 2 ^ (n * n + (n + n)) := by ring
        _ < 2 ^ (n * n + (n + n) + 1) := by
            apply pow_lt_pow_right₀ (by norm_num)
            omega
        _ = 2 ^ ((n + 1) ^ 2) := by ring_nf
    have hhalfpos : (0:ℝ) < (1 / 2 : ℝ) ^ ((n + 1) ^ 2) := by positivity
    have hnn0 : (0:ℝ) ≤ (2:ℝ) ^ (n * n) * n * n := by positivity
    calc ((2:ℝ) ^ (n * n) * n * n) * (1 - 1 / (2 * (n:ℝ))) ^ k
        ≤ ((2:ℝ) ^ (n * n) * n * n) * (1 / 2) ^ ((n + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hhalf hnn0
      _ < 2 ^ ((n + 1) ^ 2) * (1 / 2) ^ ((n + 1) ^ 2) :=
          mul_lt_mul_of_pos_right hcount hhalfpos
      _ = 1 := by rw [← mul_pow]; norm_num
  have hfac : (2 * (n:ℝ)) ^ T - (2 * (n:ℝ)) ^ (T - 1)
      = (2 * (n:ℝ)) ^ T * (1 - 1 / (2 * n)) := by
    have h1 : (2 * (n:ℝ)) ^ T = (2 * (n:ℝ)) ^ (T - 1) * (2 * n) := by
      rw [← pow_succ]
      congr 1
      omega
    field_simp
    rw [h1]
    ring
  have hposT : (0:ℝ) < ((2 * (n:ℝ)) ^ T) ^ k := by positivity
  have hmain : ((2:ℝ) ^ (n * n) * n * n) * ((2 * (n:ℝ)) ^ T - (2 * (n:ℝ)) ^ (T - 1)) ^ k
      < (2 * (n:ℝ)) ^ (k * T) := by
    rw [hfac, mul_pow, show (2 * (n:ℝ)) ^ (k * T) = ((2 * (n:ℝ)) ^ T) ^ k from pow_mul' _ _ _]
    calc ((2:ℝ) ^ (n * n) * n * n) * (((2 * (n:ℝ)) ^ T) ^ k * (1 - 1 / (2 * (n:ℝ))) ^ k)
        = (((2:ℝ) ^ (n * n) * n * n) * (1 - 1 / (2 * (n:ℝ))) ^ k) * ((2 * (n:ℝ)) ^ T) ^ k := by
          ring
      _ < 1 * ((2 * (n:ℝ)) ^ T) ^ k := mul_lt_mul_of_pos_right hkey hposT
      _ = ((2 * (n:ℝ)) ^ T) ^ k := one_mul _
  have hcast1 : ((2 ^ (n * n) * n * n * ((2 * n) ^ T - (2 * n) ^ (T - 1)) ^ k : ℕ) : ℝ)
      = ((2:ℝ) ^ (n * n) * n * n) * ((2 * (n:ℝ)) ^ T - (2 * (n:ℝ)) ^ (T - 1)) ^ k := by
    push_cast [Nat.cast_sub hNle]
    ring
  have hcast2 : (((2 * n) ^ utsLen n : ℕ) : ℝ) = (2 * (n:ℝ)) ^ (k * T) := by
    rw [show utsLen n = k * T from rfl]
    push_cast
    ring
  rw [← Nat.cast_lt (α := ℝ), hcast1, hcast2]
  exact hmain


/-- **Existence of universal traversal sequences.**  For every `n ≥ 1` there is a label
sequence of length `utsLen n = O(n⁷)` which traverses every connected component of
every undirected graph on `n` vertices, from every starting point. -/
