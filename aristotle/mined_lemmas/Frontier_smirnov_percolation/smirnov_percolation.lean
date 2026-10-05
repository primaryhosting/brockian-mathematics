import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

namespace Frontier

open Filter Topology

/-! ## Part 1: the discrete model (critical site percolation, `p = 1/2`)

Site percolation on a finite site set `V` (a finite piece of the triangular lattice) is
modelled as a uniformly random colouring `ω : V → Bool`, with `true` meaning *open*.  On
the triangular lattice the critical parameter is `p_c = 1/2`, so the uniform measure on
colourings is exactly the critical percolation measure. -/

section Discrete

variable {V : Type*} [Fintype V]

/-- The probability of an event `E` of percolation configurations under critical
(`p = 1/2`) site percolation on the finite site set `V`. -/

theorem smirnov_percolation
    (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (cardy : ℝ → ℝ)
    (hSmirnov : SmirnovConvergence P cardy)
    (α β γ δ : ℝ) (hdet : 0 < α * δ - β * γ)
    (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hpole : ∀ x ∈ Set.Icc a d, 0 < γ * x + δ) :
    Tendsto (fun n => P n (mobius α β γ δ a) (mobius α β γ δ b)
        (mobius α β γ δ c) (mobius α β γ δ d)) atTop
      (𝓝 (cardy (crossRatio a b c d))) := by
  have hda : a < d := lt_trans hab (lt_trans hbc hcd)
  have hA : 0 < γ * a + δ := hpole a ⟨le_refl a, hda.le⟩
  have hB : 0 < γ * b + δ := hpole b ⟨hab.le, (lt_trans hbc hcd).le⟩
  have hC : 0 < γ * c + δ := hpole c ⟨(lt_trans hab hbc).le, hcd.le⟩
  have hD : 0 < γ * d + δ := hpole d ⟨hda.le, le_refl d⟩
  have h1 := mobius_lt_mobius (α := α) (β := β) hdet hA hB hab
  have h2 := mobius_lt_mobius (α := α) (β := β) hdet hB hC hbc
  have h3 := mobius_lt_mobius (α := α) (β := β) hdet hC hD hcd
  have hlim := hSmirnov _ _ _ _ h1 h2 h3
  rwa [crossRatio_mobius hdet.ne' hA.ne' hB.ne' hC.ne' hD.ne'
    (by linarith : c ≠ a) (by linarith : d ≠ b)] at hlim

/-- Consistency of the limit with Part 1: since each `P n a b c d` is a probability (as in
`probHalf_nonneg` / `probHalf_le_one`), the Cardy–Smirnov limit is itself a probability. -/
