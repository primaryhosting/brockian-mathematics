import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-!
## Setting

We work with the standard `m`-fold dilated `n`-dimensional simplex

  `Δ = { v : ℕ^{n+1} | v 0 + ... + v n = m }`

described in *partial sum coordinates*: a vertex is encoded by the function
`s : ℕ → ℕ` with `s j = v 0 + ... + v (j-1)`, so that `s 0 = 0`, `s` is monotone,
and `s j = m` for `j > n`.  The barycentric coordinate `v i` is `s (i+1) - s i`.

The triangulation is the classical Freudenthal–Kuhn triangulation: a maximal cell
is given by a base vertex `s` together with an ordering of the `n` coordinates
`1, …, n`; the ordering is encoded by the function `p : ℕ → ℕ` sending a coordinate
`j ∈ [1,n]` to the step `p j ∈ [0,n-1]` at which it is incremented.  The `k`-th
vertex of the cell is then `wv n s p k`.
-/

/-- `Reg n m s` says that `s` encodes a vertex of the `m`-fold dilated standard
`n`-simplex, in partial sum coordinates. -/

def IsRainbowCell (n m : ℕ) (c : (ℕ → ℕ) → ℕ) (s p : ℕ → ℕ) : Prop :=
  IsCell n m s p ∧ ∀ i ≤ n, ∃ k ≤ n, c (wv n s p k) = i

/-!
## Basic facts about `Reg`
-/

