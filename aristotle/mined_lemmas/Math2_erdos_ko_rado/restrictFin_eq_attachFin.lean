import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of `[n] = Fin n`
with `2 * k ≤ n` has at most `(n - 1).choose (k - 1)` members.

This is obtained from Mathlib's `Finset.erdos_ko_rado`
(`Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`), which is stated using
`Set.Intersecting` and `Set.Sized`. -/

private lemma restrictFin_eq_attachFin {n : ℕ} {A : Finset ℕ} (hA : ∀ m ∈ A, m < n) :
    restrictFin n A = A.attachFin hA := by
  ext i
  simp [restrictFin, Finset.mem_attachFin]

