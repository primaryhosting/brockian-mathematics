import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


theorem isEquidecomposable_sdiff_of_iterates (A D : Set X) (g : G)
    (hmem : ∀ (n : ℕ) (x : X), x ∈ D → (g ^ n) • x ∈ A)
    (hdisj : ∀ (n : ℕ), 1 ≤ n → ∀ x ∈ D, (g ^ n) • x ∉ D) :
    IsEquidecomposable G A (A \ D) := by
  classical
  set Es : Set X := ⋃ n : ℕ, (fun x => (g ^ n) • x) '' D with hEs
  have hmemE : ∀ y : X, y ∈ Es ↔ ∃ n : ℕ, ∃ x ∈ D, (g ^ n) • x = y := by
    intro y
    simp only [hEs, Set.mem_iUnion, Set.mem_image]
  have hDE : D ⊆ Es := by
    intro x hx
    rw [hmemE]
    exact ⟨0, x, hx, by simp⟩
  have hEA : Es ⊆ A := by
    intro y hy
    obtain ⟨n, x, hx, rfl⟩ := (hmemE y).1 hy
    exact hmem n x hx
  have hgE : ∀ y ∈ Es, g • y ∈ Es ∧ g • y ∉ D := by
    intro y hy
    obtain ⟨n, x, hx, rfl⟩ := (hmemE y).1 hy
    have hnext : (g ^ (n + 1)) • x = g • (g ^ n) • x := by rw [pow_succ']; exact mul_smul _ _ _
    refine ⟨(hmemE _).2 ⟨n + 1, x, hx, hnext⟩, ?_⟩
    rw [← hnext]
    exact hdisj (n + 1) (by omega) x hx
  have hginv : ∀ y ∈ Es, y ∉ D → g⁻¹ • y ∈ Es := by
    intro y hy hyD
    obtain ⟨n, x, hx, rfl⟩ := (hmemE y).1 hy
    cases n with
    | zero => exact absurd (by simpa using hx) hyD
    | succ m =>
        have hnext : (g ^ (m + 1)) • x = g • (g ^ m) • x := by rw [pow_succ']; exact mul_smul _ _ _
        rw [hnext, inv_smul_smul]
        exact (hmemE _).2 ⟨m, x, hx, rfl⟩
  refine ⟨⟨⟨fun x => if x ∈ Es then g • x else x, fun y => if y ∈ Es then g⁻¹ • y else y,
      A, A \ D, ?_, ?_, ?_, ?_⟩, ?_⟩, rfl, rfl⟩
  · intro x hx
    by_cases hxE : x ∈ Es
    · simp only [hxE, if_true]
      exact ⟨hEA (hgE x hxE).1, (hgE x hxE).2⟩
    · simp only [hxE, if_false]
      exact ⟨hx, fun hxD => hxE (hDE hxD)⟩
  · rintro y ⟨hy, hyD⟩
    by_cases hyE : y ∈ Es
    · simp only [hyE, if_true]
      exact hEA (hginv y hyE hyD)
    · simp only [hyE, if_false]
      exact hy
  · intro x hx
    by_cases hxE : x ∈ Es
    · simp only [hxE, if_true, (hgE x hxE).1, inv_smul_smul]
    · simp only [hxE, if_false]
  · rintro y ⟨hy, hyD⟩
    by_cases hyE : y ∈ Es
    · simp only [hyE, if_true, hginv y hyE hyD, smul_inv_smul]
    · simp only [hyE, if_false]
  · refine ⟨{1, g}, ?_⟩
    intro x _
    by_cases hxE : x ∈ Es
    · exact ⟨g, by simp, by simp [hxE]⟩
    · exact ⟨1, by simp, by simp [hxE]⟩

end Algebra

end Frontier

