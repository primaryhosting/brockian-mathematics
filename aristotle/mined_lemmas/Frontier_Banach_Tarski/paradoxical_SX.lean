import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem paradoxical_SX : Paradoxical (E ≃ₗᵢ[ℝ] E) SX := by
  obtain ⟨A, hdisj, hunion, hd1, hu1, hd2, hu2⟩ := freeGroup_paradoxical
  refine ⟨XA (A 0) ∪ XA (A 1), XA (A 2) ∪ XA (A 3), ?_, ?_, ?_, ?_⟩
  · rw [← XA_union, ← XA_union, ← XA_union, ← XA_univ]
    congr 1
    rw [← hunion]
    ext w
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ((h | h) | (h | h))
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
    · rintro ⟨i, hi⟩
      fin_cases i
      exacts [Or.inl (Or.inl hi), Or.inl (Or.inr hi), Or.inr (Or.inl hi), Or.inr (Or.inr hi)]
  · rw [← XA_union, ← XA_union]
    refine XA_disjoint ?_
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hdisj 0 2 (by decide), hdisj 0 3 (by decide)⟩,
      hdisj 1 2 (by decide), hdisj 1 3 (by decide)⟩
  · have hsm : Equidec (E ≃ₗᵢ[ℝ] E) (XA (A 1)) ((phi (FreeGroup.of 0)) • XA (A 1)) :=
      Equidec.smul_set _ _
    have h := Equidec.union (XA_disjoint (hdisj 0 1 (by decide)))
      (by
        rw [XA_smul]
        refine XA_disjoint ?_
        have : (fun w => FreeGroup.of (0 : Fin 2) * w) '' A 1 = FreeGroup.of (0 : Fin 2) • A 1 :=
          rfl
        rw [this]
        exact hd1)
      (Equidec.refl (XA (A 0))) hsm
    have heq : A 0 ∪ (fun w => FreeGroup.of (0 : Fin 2) * w) '' A 1 = Set.univ := hu1
    have hunion2 : XA (A 0) ∪ XA ((fun w => FreeGroup.of (0 : Fin 2) * w) '' A 1) = SX := by
      rw [← XA_union, heq, XA_univ]
    rw [XA_smul, hunion2] at h
    exact h
  · have hsm : Equidec (E ≃ₗᵢ[ℝ] E) (XA (A 3)) ((phi (FreeGroup.of 1)) • XA (A 3)) :=
      Equidec.smul_set _ _
    have h := Equidec.union (XA_disjoint (hdisj 2 3 (by decide)))
      (by
        rw [XA_smul]
        refine XA_disjoint ?_
        have : (fun w => FreeGroup.of (1 : Fin 2) * w) '' A 3 = FreeGroup.of (1 : Fin 2) • A 3 :=
          rfl
        rw [this]
        exact hd2)
      (Equidec.refl (XA (A 2))) hsm
    have heq : A 2 ∪ (fun w => FreeGroup.of (1 : Fin 2) * w) '' A 3 = Set.univ := hu2
    have hunion2 : XA (A 2) ∪ XA ((fun w => FreeGroup.of (1 : Fin 2) * w) '' A 3) = SX := by
      rw [← XA_union, heq, XA_univ]
    rw [XA_smul, hunion2] at h
    exact h

/-- The sphere is equidecomposable with the sphere minus the poles. -/
