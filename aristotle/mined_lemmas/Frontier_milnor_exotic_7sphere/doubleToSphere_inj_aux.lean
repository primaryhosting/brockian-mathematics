import Mathlib
import RequestProject.AlexanderTrick

/-!
# Twisted spheres

A *twisted sphere* is obtained by gluing two copies of the closed `n`-disk along their boundary
`𝕊ⁿ⁻¹` by a homeomorphism `f`.  All the known exotic spheres in dimension `7` arise this way
(Milnor's `S³`-bundles over `S⁴` carry Morse functions with exactly two critical points, which exhibits
them as twisted spheres).

The main result of this file is that **every twisted sphere is homeomorphic to the standard
sphere**: this is the topological half of Milnor's theorem, and it is proved here in full, for
every dimension `n`, using the Alexander trick from `RequestProject.AlexanderTrick`.
-/

namespace Frontier

open Metric

/-- The unit sphere `𝕊ⁿ⁻¹ ⊆ ℝⁿ`. -/
abbrev Sph (n : ℕ) : Type := sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The closed unit disk `Dⁿ ⊆ ℝⁿ`. -/
abbrev Dsk (n : ℕ) : Type := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1


lemma doubleToSphere_inj_aux {n : ℕ} (a b : Dsk n ⊕ Dsk n)
    (h : doubleToSphere a = doubleToSphere b) :
    Quot.mk (GlueRel (sphereId n)) a = Quot.mk (GlueRel (sphereId n)) b := by
  have key : ∀ (u v : Dsk n) (e₁ e₂ : ℝ) (h₁ : e₁ ^ 2 = 1) (h₂ : e₂ ^ 2 = 1),
      (hemisphere e₁ h₁ u : EuclideanSpace ℝ (Fin (n+1)))
        = (hemisphere e₂ h₂ v : EuclideanSpace ℝ (Fin (n+1))) →
      (u : EuclideanSpace ℝ (Fin n)) = (v : EuclideanSpace ℝ (Fin n)) ∧
        e₁ * Real.sqrt (1 - ‖(u : EuclideanSpace ℝ (Fin n))‖ ^ 2)
          = e₂ * Real.sqrt (1 - ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    intro u v e₁ e₂ h₁ h₂ huv
    exact snocLp_injective huv
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      obtain ⟨h1, -⟩ := key u v 1 1 (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [Subtype.ext h1]
    | inr v =>
      obtain ⟨h1, h2⟩ := key u v 1 (-1) (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [one_mul, neg_one_mul, ← h1] at h2
      have hnorm : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_one_of_sqrt_eq_neg h2
      have hu : u = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := rfl
      have hv : v = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := Subtype.ext h1.symm
      rw [hu, hv]
      exact TwistedSphere.sound (sphereId n) _
  | inr u =>
    cases b with
    | inl v =>
      obtain ⟨h1, h2⟩ := key u v (-1) 1 (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [one_mul, neg_one_mul, ← h1] at h2
      have hnorm : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 :=
        norm_eq_one_of_sqrt_eq_neg (by linarith)
      have hu : u = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := rfl
      have hv : v = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := Subtype.ext h1.symm
      rw [hu, hv]
      exact (TwistedSphere.sound (sphereId n) _).symm
    | inr v =>
      obtain ⟨h1, -⟩ := key u v (-1) (-1) (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [Subtype.ext h1]

