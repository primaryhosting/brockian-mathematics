/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem exists_absorbing_rotation {D : Set E} (hD : D ⊆ sph) (hcount : D.Countable) :
    ∃ rho : SO3, ∀ n : ℕ, 1 ≤ n → Disjoint ((rho ^ n) • D) D := by
  obtain ⟨Q, hQ1, hQ2⟩ := exists_axis hcount
  have hD'sub : (Q⁻¹ • D : Set E) ⊆ sph := by
    rintro _ ⟨d, hd, rfl⟩; exact smul_mem_sph _ (hD hd)
  have hD'c : (Q⁻¹ • D : Set E).Countable := hcount.image _
  obtain ⟨t, ht⟩ := exists_angle hD'sub hD'c hQ1 hQ2
  have hpow : ∀ n : ℕ, (Q * rZ t * Q⁻¹) ^ n = Q * (rZ t ^ n) * Q⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, pow_succ]; group
  refine ⟨Q * rZ t * Q⁻¹, fun n hn => ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨d, hd, rfl⟩ hmem
  have h1 : Q⁻¹ • ((Q * rZ t * Q⁻¹) ^ n • d) = (rZ t ^ n) • (Q⁻¹ • d) := by
    rw [hpow, ← SemigroupAction.mul_smul, ← SemigroupAction.mul_smul]
    congr 1
    group
  have hin1 : Q⁻¹ • ((Q * rZ t * Q⁻¹) ^ n • d) ∈ (Q⁻¹ • D : Set E) := ⟨_, hmem, rfl⟩
  have hin2 : (rZ t ^ n) • (Q⁻¹ • d) ∈ (rZ t ^ n) • (Q⁻¹ • D : Set E) :=
    ⟨Q⁻¹ • d, ⟨d, hd, rfl⟩, rfl⟩
  rw [h1] at hin1
  exact ((ht n hn).le_bot ⟨hin2, hin1⟩ : _ ∈ (⊥ : Set E))

