/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

open MeasureTheory Set Real

/-! ## Mirzakhani's integration kernel

Mirzakhani's recursion for Weil–Petersson volumes of moduli spaces of bordered
hyperbolic surfaces is driven by the kernel

`H (x, t) = 1 / (1 + exp ((x + t) / 2)) + 1 / (1 + exp ((x - t) / 2))`.

We write `wpPhi u = 1 / (1 + exp (u / 2))`, so that `H (x, t) = wpPhi (x+t) + wpPhi (x-t)`.
-/

/-- The basic Fermi–Dirac type profile `u ↦ 1 / (1 + e^{u/2})` out of which Mirzakhani's
integration kernel is built. -/

theorem altBasel : HasSum (fun n : ℕ => (-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 12) := by
  have hS : HasSum (fun n : ℕ => 1 / ((n:ℝ)) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hE : HasSum (fun k : ℕ => 1 / (((2 * k : ℕ)) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    have h4 := hS.mul_left (1 / 4)
    have he : (fun i : ℕ => (1:ℝ) / 4 * (1 / (i:ℝ) ^ 2))
        = fun k : ℕ => 1 / (((2 * k : ℕ)) : ℝ) ^ 2 := by
      funext k; push_cast; ring
    rw [he] at h4
    convert h4 using 1; ring
  have hOs : Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h; simp only [] at h; omega
    exact hS.summable.comp_injective hinj
  have h := HasSum.even_add_odd (f := fun n : ℕ => 1 / ((n:ℝ)) ^ 2) hE hOs.hasSum
  have hval : Real.pi ^ 2 / 24 + (∑' k : ℕ, 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) = Real.pi ^ 2 / 6 :=
    (hS.unique h).symm
  have hO : HasSum (fun k : ℕ => 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
    have he : (∑' k : ℕ, 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) = Real.pi ^ 2 / 8 := by linarith
    exact he ▸ hOs.hasSum
  set g : ℕ → ℝ := fun m => -((-1:ℝ) ^ m) / (m:ℝ) ^ 2 with hg
  have h0 : g 0 = 0 := by simp [hg]
  have hgE : HasSum (fun k : ℕ => g (2 * k)) (-(Real.pi ^ 2 / 24)) := by
    have h1 := hE.mul_left (-1)
    have he : (fun k : ℕ => (-1:ℝ) * (1 / (((2 * k : ℕ)) : ℝ) ^ 2)) = fun k : ℕ => g (2 * k) := by
      funext k; simp only [hg, pow_mul]; push_cast; ring
    rw [he] at h1
    convert h1 using 1; ring
  have hgO : HasSum (fun k : ℕ => g (2 * k + 1)) (Real.pi ^ 2 / 8) := by
    have he : (fun k : ℕ => 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) = fun k : ℕ => g (2 * k + 1) := by
      funext k; simp only [hg, pow_succ, pow_mul]; push_cast; ring
    rw [he] at hO
    exact hO
  have hgsum : HasSum g ((-(Real.pi ^ 2 / 24) + Real.pi ^ 2 / 8) + ∑ i ∈ Finset.range 1, g i) := by
    simpa [h0] using hgE.even_add_odd hgO
  have hshift := (hasSum_nat_add_iff (f := g) 1).2 hgsum
  have he2 : (fun n : ℕ => g (n + 1)) = fun n : ℕ => (-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 2 := by
    funext n; simp only [hg, pow_succ]; push_cast; ring
  rw [he2] at hshift
  convert hshift using 1
  ring

