import Mathlib

/-!
# Arithmetic core for the freeness of two rotations of `SO(3)`

We consider the two rotations of `ℝ³`

```
σ = 1/3 * ![![1, -2√2, 0], ![2√2, 1, 0], ![0,0,3]]      (rotation about the z-axis)
τ = 1/3 * ![![3, 0, 0], ![0, 1, -2√2], ![0, 2√2, 1]]    (rotation about the x-axis)
```

both by the angle `arccos (1/3)`.  Applying a word of length `n` in `σ^{±1}, τ^{±1}` to the
vector `(1, 0, 1)` produces a vector of the form `3⁻ⁿ • (a, b√2, c)` with `a b c : ℤ`.
This file contains the purely arithmetic heart of the matter: for a nonempty *reduced* word,
the middle coordinate `b` is not divisible by `3`; in particular it is nonzero.
-/

namespace BanachTarski

/-- A letter: the first component selects the generator (`false` = `σ`, `true` = `τ`),
the second component is the sign of the exponent (`true` = `+1`). -/
abbrev Ltr := Bool × Bool

/-- The action of a letter on the integer triple `(a, b, c)` representing the vector
`3⁻ⁿ • (a, b√2, c)`; the factor `3⁻¹` is not recorded here. -/

theorem not_dvd_stv : ∀ (L : List Ltr), Reduced L → L ≠ [] → ¬ ((3 : ℤ) ∣ (stv L).2.1) := by
  intro L
  induction L with
  | nil => intro _ h; exact absurd rfl h
  | cons g L ih =>
    intro hred _
    match L with
    | [] =>
      obtain ⟨x, s⟩ := g
      cases x <;> cases s <;> decide
    | g' :: L' =>
      have hIH : ¬ ((3 : ℤ) ∣ (stv (g' :: L')).2.1) :=
        ih hred.tail (by simp)
      have hnc : NonCancel g g' := hred.rel
      obtain ⟨x, s⟩ := g
      obtain ⟨x', s'⟩ := g'
      rcases hv : stv L' with ⟨a, b, c⟩
      rw [stv_cons, hv] at hIH
      rw [stv_cons, stv_cons, hv]
      cases x <;> cases s <;> cases x' <;> cases s' <;>
        simp only [st, NonCancel] at hIH hnc ⊢ <;>
        first
          | omega
          | simp at hnc
end BanachTarski

import Mathlib

/-!
# Equidecomposability and paradoxical sets

Given a group `G` of permutations of a type `X`, two sets `A B : Set X` are *`G`-equidecomposable*
if `A` can be cut into finitely many pieces which, after moving each piece by an element of `G`,
form a partition of `B`.

A set `E` is *`G`-paradoxical* if it contains two disjoint subsets, each of which is
`G`-equidecomposable with `E` itself.
-/

namespace BanachTarski

open Function Set

variable {X : Type*}

/-- `EqDecomp G A B` : the sets `A` and `B` are equidecomposable using elements of the
permutation group `G`. -/
