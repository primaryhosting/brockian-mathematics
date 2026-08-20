import Mathlib
/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE FILE HEADER.  Lean 4 requires `import` to be the very first command of a
module, so the requested `/-! ... -/` module docstring is placed immediately after the
single `import Mathlib` line rather than before it; its text is otherwise verbatim.
-/

open scoped BigOperators

namespace Frontier

/-! ## The superrigidity extension property

Margulis superrigidity says, for `G` a semisimple Lie group of real rank `≥ 2`, `Γ ≤ G` an
irreducible lattice and `π : Γ → H` a homomorphism into a simple algebraic group with
unbounded Zariski-dense image, that `π` is the restriction of a *continuous* homomorphism
`G → H`.  The predicate below isolates the conclusion of that theorem: a homomorphism
defined on the lattice extends to a continuous homomorphism of the ambient group.
-/

/-- The conclusion of a superrigidity statement, in additive notation: a homomorphism `π`
defined on a lattice `L` (mapped into the ambient group `G` by the inclusion `ι`) is the
restriction along `ι` of a continuous homomorphism `G → H`. -/

lemma exists_reduce_column {m : ℕ} (hm : m < n) (hm2 : m + 1 < n) (N : ℕ) :
    ∀ A : Matrix.SpecialLinearGroup (Fin n) ℤ, PartialId m (A : Matrix (Fin n) (Fin n) ℤ) →
      colMeasure m hm (A : Matrix (Fin n) (Fin n) ℤ) ≤ N →
      ∃ g ∈ ESub n, PartialId m ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) ∧
        ∀ i : Fin n, ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0 := by
  classical
  induction N with
  | zero =>
      intro A hA hmeas
      exfalso
      have hz : ∀ i : Fin n, m ≤ (i : ℕ) → (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = 0 := by
        intro i hi
        have hmem : i ∈ Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ) := by simp [hi]
        have hsum : ∑ i ∈ Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ),
            ((A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩).natAbs = 0 := Nat.le_zero.1 hmeas
        have := (Finset.sum_eq_zero_iff.1 hsum) i hmem
        simpa [Int.natAbs_eq_zero] using this
      have h0 : IsUnit (0 : ℤ) :=
        column_isUnit_of_dvd hm A hA 0 fun i hi => by rw [hz i hi]
      simp at h0
  | succ N ih =>
      intro A hA hmeas
      set S : Finset (Fin n) := Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ) with hS
      set T : Finset (Fin n) :=
        S.filter fun i => (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ ≠ 0 with hT
      have hmemS : ∀ i : Fin n, i ∈ S ↔ m ≤ (i : ℕ) := by intro i; simp [hS]
      have hmemT : ∀ i : Fin n, i ∈ T ↔
          (m ≤ (i : ℕ) ∧ (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ ≠ 0) := by
        intro i; simp [hT, hS]
      by_cases hcard : 1 < T.card
      · obtain ⟨p, hpT, hpmax⟩ := T.exists_max_image
          (fun i => ((A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩).natAbs)
          (Finset.card_pos.1 (by omega))
        obtain ⟨q, hqT, hqp⟩ := Finset.exists_mem_ne hcard p
        have hp := (hmemT p).1 hpT
        have hq := (hmemT q).1 hqT
        have hpq : p ≠ q := fun h => hqp h.symm
        set a : ℤ := (A : Matrix (Fin n) (Fin n) ℤ) p ⟨m, hm⟩ with ha
        set b : ℤ := (A : Matrix (Fin n) (Fin n) ℤ) q ⟨m, hm⟩ with hb
        set g1 : Matrix.SpecialLinearGroup (Fin n) ℤ := elemSL p q hpq (-(a / b)) with hg1
        have hA1 : PartialId m ((g1 * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) := partialId_rowOp hA hpq hp.1 hq.1 _
        have hentry : ∀ i : Fin n, ((g1 * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ =
            if i = p then a % b else (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ := by
          intro i
          rw [hg1, elemSL_mul_apply]
          by_cases hip : i = p
          · rw [if_pos hip, if_pos hip, Int.emod_def]
            ring
          · rw [if_neg hip, if_neg hip]
        have hlt : colMeasure m hm ((g1 * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) < colMeasure m hm (A : Matrix (Fin n) (Fin n) ℤ) := by
          refine Finset.sum_lt_sum (fun i _ => ?_) ⟨p, (hmemS p).2 hp.1, ?_⟩
          · rw [hentry i]
            by_cases hip : i = p
            · subst hip
              rw [if_pos rfl]
              exact le_of_lt (lt_of_lt_of_le (natAbs_emod_lt hq.2) (hpmax q hqT))
            · rw [if_neg hip]
          · rw [hentry p, if_pos rfl]
            exact lt_of_lt_of_le (natAbs_emod_lt hq.2) (hpmax q hqT)
        obtain ⟨g, hg, hgp, hgc⟩ := ih _ hA1 (Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hmeas))
        refine ⟨g * g1, mul_mem hg (elemSL_mem_ESub _ _ _ _), ?_, ?_⟩
        · rwa [mul_assoc]
        · rw [mul_assoc]
          exact hgc
      · push_neg at hcard
        rcases Nat.lt_or_ge T.card 1 with hc0 | hc1
        · exfalso
          have hTe : T = ∅ := Finset.card_eq_zero.1 (by omega)
          have hz : ∀ i : Fin n, m ≤ (i : ℕ) →
              (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = 0 := by
            intro i hi
            by_contra hne
            have : i ∈ T := (hmemT i).2 ⟨hi, hne⟩
            rw [hTe] at this
            simp at this
          have h0 : IsUnit (0 : ℤ) :=
            column_isUnit_of_dvd hm A hA 0 fun i hi => by rw [hz i hi]
          simp at h0
        · obtain ⟨p, hTp⟩ := (Finset.card_eq_one (s := T)).1 (by omega)
          have hpT : p ∈ T := by rw [hTp]; simp
          have hp := (hmemT p).1 hpT
          refine exists_reduce_column_of_single hm hm2 A hA p hp.1 fun i hi hip => ?_
          by_contra hne
          have : i ∈ T := (hmemT i).2 ⟨hi, hne⟩
          rw [hTp] at this
          exact hip (Finset.mem_singleton.1 this)

/-- Clearing the pivot row to the right of the pivot by elementary column operations. -/
