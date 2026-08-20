import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope note.  Mathlib (at the version pinned by this project) contains no sunflower lemma:
searching for `sunflower` / `Sunflower` turns up nothing, and `exact?`/`apply?` have nothing
to offer on the statement below, so the development here is self-contained.

The bound proved as `Math2.sunflower_bound` is the classical Erdős–Rado bound
`k! * (r-1)^k`.  The Alweiss–Lovett–Wu–Zhang improvement to `(C * r * log k)^k` is *not*
established here; `Math2.sunflower_bound_pow` only records the convenient weakening
`(k * r)^k` of the Erdős–Rado bound.

`import Mathlib` has to precede the header comment above because Lean 4 requires `import`
commands to come first in a file (a `/-! -/` module docstring before them is rejected).
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

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower* with core `core` when any two distinct
members of `S` meet exactly in `core`. -/

lemma exists_max_pairwise_disjoint (F : Finset (Finset α)) :
    ∃ D ⊆ F, PairwiseDisjointFamily D ∧
      ∀ D' ⊆ F, PairwiseDisjointFamily D' → D'.card ≤ D.card := by
  classical
  set P : Finset (Finset (Finset α)) :=
    (F.powerset).filter (fun D => PairwiseDisjointFamily D) with hP
  have hne : P.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [hP, PairwiseDisjointFamily]
  obtain ⟨D, hDmem, hDmax⟩ := P.exists_max_image Finset.card hne
  simp only [hP, Finset.mem_filter, Finset.mem_powerset] at hDmem
  refine ⟨D, hDmem.1, hDmem.2, ?_⟩
  intro D' hD' hD'disj
  exact hDmax D' (by simp [hP, Finset.mem_filter, Finset.mem_powerset, hD', hD'disj])

/-- **Erdős–Rado sunflower lemma.**  A `k`-uniform family with more than `k! (r-1)^k`
members contains a sunflower with `r` petals. -/
