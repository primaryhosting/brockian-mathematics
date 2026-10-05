import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/

theorem pell_13_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 13 * p.2 ^ 2 = 1}.Infinite := by
  have hinj : Function.Injective pellSol := by
    intro m n hmn
    exact pellSol_snd_strictMono.injective (congrArg Prod.snd hmn)
  have hrange : Set.range pellSol ⊆ {p : ℤ × ℤ | p.1 ^ 2 - 13 * p.2 ^ 2 = 1} := by
    rintro p ⟨n, rfl⟩
    exact pellSol_isSol n
  exact Set.Infinite.mono hrange (Set.infinite_range_of_injective hinj)

end Math

/-!
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 13`.**
`x² - 13·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently, a solution other than `(±1, 0)`).
The fundamental solution is `(x, y) = (649, 180)`:
`649² = 421201 = 13 · 180² + 1 = 13 · 32400 + 1`. -/
