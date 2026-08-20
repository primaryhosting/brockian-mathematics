import Mathlib

/-!
# Equivariance of the regular `n`-gon representation of the dihedral group

This file generalises the pentagon (`n = 5`, dihedral group `D₅`) picture to an arbitrary
regular `n`-gon.

The combinatorial model of the vertices of the `n`-gon is `ZMod n`, on which the dihedral group
`DihedralGroup n` acts by `r i • k = k + i` (rotation) and `sr i • k = -i - k` (reflection).

The geometric model is the set of `n`-th roots of unity in `ℂ`, on which `DihedralGroup n` acts by
`r i • z = ζ^i * z` and `sr i • z = ζ^(-i) * conj z`, where `ζ = exp (2πI / n)`.

The main result, `Brockian.PentagonPentagonEquivarianceGeneral`, says that the vertex map
`k ↦ exp (2πI k / n)` intertwines the two actions, for every `n > 0`.  The pentagon case is
recorded as `Brockian.pentagon_equivariance`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

open Complex

/-- The character `E n m = exp (2 π i m / n)`. -/

lemma planeAct_mul (n : ℕ) (hn : 0 < n) (g h : DihedralGroup n) (z : ℂ) :
    planeAct n (g * h) z = planeAct n g (planeAct n h z) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ a b : ℤ, rootExp n a * rootExp n b = rootExp n (a + b) := by
    intro a b; rw [rootExp_add]
  have cast_val : ∀ i : ZMod n, ((i.val : ℤ) : ZMod n) = i := by
    intro i; push_cast; simp [ZMod.natCast_val]
  cases g with
  | r i =>
    cases h with
    | r j =>
      show rootExp n (((i + j).val : ℤ)) * z = _
      have : rootExp n (((i + j : ZMod n).val : ℤ)) = rootExp n ((i.val : ℤ) + (j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct]
      ring
    | sr j =>
      show rootExp n (-(((j - i : ZMod n)).val : ℤ)) * (starRingEnd ℂ) z = _
      have : rootExp n (-(((j - i : ZMod n)).val : ℤ))
          = rootExp n ((i.val : ℤ) + -(j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct]
      ring
  | sr i =>
    cases h with
    | r j =>
      show rootExp n (-(((i + j : ZMod n)).val : ℤ)) * (starRingEnd ℂ) z = _
      have : rootExp n (-(((i + j : ZMod n)).val : ℤ))
          = rootExp n (-(i.val : ℤ) + -(j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct, conj_rootExp]
      ring
    | sr j =>
      show rootExp n (((j - i : ZMod n)).val : ℤ) * z = _
      have : rootExp n (((j - i : ZMod n)).val : ℤ)
          = rootExp n (-(i.val : ℤ) + (j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct, conj_rootExp]
      ring

/-- **Equivariance of the regular `n`-gon representation.**  For every `n > 0`, the vertex map
`ZMod n → ℂ`, `k ↦ exp (2 π i k / n)`, intertwines the combinatorial action of the dihedral
group `DihedralGroup n` on the vertex labels with its geometric action on the plane.  This
generalises the `D₅`/pentagon case to arbitrary `n`-gons. -/
