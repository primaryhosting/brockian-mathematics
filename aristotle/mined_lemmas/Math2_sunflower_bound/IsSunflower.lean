/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- A family of sets `S` is a *sunflower* if all pairwise intersections of distinct
members are equal to a common `core`. -/

def IsSunflower {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : Prop :=
  ∃ core : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = core

/-!
### Statement and status

`Math2.sunflower_bound` below is the **Erdős–Rado sunflower lemma**: every family `F` of
`w`-element sets with `w ! * (r - 1) ^ w < F.card` contains a sunflower with `r` petals.

The Alweiss–Lovett–Wu–Zhang improvement asserts the stronger bound

```
∃ C : ℝ, ∀ w r F, (∀ A ∈ F, A.card = w) → (C * r * Real.log w) ^ w < F.card →
  ∃ S ⊆ F, S.card = r ∧ IsSunflower S
```

which is *not* established in this file; only the classical bound above is proved here.
-/

/-- **Erdős–Rado sunflower lemma.**  If every member of the family `F` of finite sets has
exactly `w` elements and `F` has more than `w ! * (r - 1) ^ w` members, then `F` contains a
sunflower with `r` petals, i.e. `r` distinct members whose pairwise intersections all equal a
common core. -/
