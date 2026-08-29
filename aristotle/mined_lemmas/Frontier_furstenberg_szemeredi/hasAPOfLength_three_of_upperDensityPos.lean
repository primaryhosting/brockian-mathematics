import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `A` contains an arithmetic progression of length `k`, i.e. there are `a` and a positive
common difference `d` with `a, a + d, …, a + (k-1) * d` all in `A`. -/

theorem hasAPOfLength_three_of_upperDensityPos {A : Set ℕ} (hA : UpperDensityPos A) :
    HasAPOfLength A 3 := by
  obtain ⟨δ, hδ, hA⟩ := hA
  obtain ⟨N₀, hN₀⟩ := rothNumberNat_le_eventually (half_pos hδ)
  obtain ⟨M, hM, hcard⟩ := hA (max N₀ 1)
  have hM₀ : N₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : (1 : ℕ) ≤ M := le_trans (le_max_right _ _) hM
  set s : Finset ℕ := (Finset.range M).filter (fun n => n ∈ A) with hs
  have hnot : ¬ ThreeAPFree (s : Set ℕ) := by
    intro hfree
    have hle : s.card ≤ rothNumberNat M :=
      hfree.le_rothNumberNat s (fun x hx => lt_of_mem_prefixFinset hx) rfl
    have h1 : δ * M ≤ (rothNumberNat M : ℝ) := by
      refine le_trans hcard ?_
      exact_mod_cast hle
    have h2 : (rothNumberNat M : ℝ) ≤ δ / 2 * M := hN₀ M hM₀
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
    nlinarith
  rw [ThreeAPFree] at hnot
  push_neg at hnot
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hne⟩ := hnot
  refine hasAPOfLength_three_of_average (A := A) ?_ ?_ ?_ hxyz hne
  · exact mem_of_mem_prefixFinset (Finset.mem_coe.mp hx)
  · exact mem_of_mem_prefixFinset (Finset.mem_coe.mp hy)
  · exact mem_of_mem_prefixFinset (Finset.mem_coe.mp hz)

/-- **Furstenberg–Szemerédi (density case, unconditional)**: every subset of `ℕ` of positive
upper density contains arithmetic progressions of every length `k ≤ 3`; moreover the general
statement for all lengths follows, as a Lean-checked reduction, from the finitary density form
of Szemerédi's theorem. -/
