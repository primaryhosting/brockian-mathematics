/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-- The transfer map sending a set of naturals to the corresponding subset of `Fin n`. -/

private lemma card_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).card = A.card := by
  have h : ∀ m ∈ A, m < n := fun m hm => Finset.mem_range.mp (hA hm)
  have : toFin n A = A.attachFin h := by
    ext i
    simp [mem_toFin, Finset.mem_attachFin]
  rw [this, Finset.card_attachFin]

/-- **Erdős–Ko–Rado theorem.**  A `k`-uniform intersecting family of subsets of
`{0, 1, …, n-1}` with `2 * k ≤ n` has at most `(n - 1).choose (k - 1)` members.

The proof transfers the statement to `Fin n` and invokes Mathlib's
`Finset.erdos_ko_rado` (proved there via the Kruskal–Katona theorem). -/
