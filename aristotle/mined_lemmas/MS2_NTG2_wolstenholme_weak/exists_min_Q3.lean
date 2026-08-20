import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma exists_min_Q3 {G : Matrix (Fin 3) (Fin 3) ℤ} (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v) :
    ∃ w : Fin 3 → ℤ, w ≠ 0 ∧ ∀ v : Fin 3 → ℤ, v ≠ 0 → Q3 G w ≤ Q3 G v := by
  classical
  set S : Set ℕ := {k : ℕ | ∃ v : Fin 3 → ℤ, v ≠ 0 ∧ Q3 G v = (k : ℤ)} with hS
  have hne : S.Nonempty := by
    have h0 : (![1, 0, 0] : Fin 3 → ℤ) ≠ 0 := by
      intro h
      have : (![1, 0, 0] : Fin 3 → ℤ) 0 = 0 := by rw [h]; rfl
      simp at this
    refine ⟨(Q3 G ![1, 0, 0]).toNat, ![1, 0, 0], h0, ?_⟩
    have := hpd _ h0
    omega
  obtain ⟨m, hmS, hmin⟩ := Nat.lt_wfRel.wf.has_min S hne
  obtain ⟨w, hw0, hval⟩ := hmS
  refine ⟨w, hw0, ?_⟩
  intro v hv
  have hpos : 0 < Q3 G v := hpd v hv
  have hmem : (Q3 G v).toNat ∈ S := ⟨v, hv, by omega⟩
  have hle := hmin _ hmem
  simp only [Nat.lt_wfRel, not_lt] at hle
  omega

/-- A vector realizing the minimum is primitive. -/
