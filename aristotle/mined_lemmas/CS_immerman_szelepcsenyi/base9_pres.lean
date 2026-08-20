import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

lemma base9_pres {s t : CSt P.N P.V} (hs : Inv P x s) (hB : Base9 P s t)
    (hfnd : t.fnd = true ↔
      (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ) ∨
        P.step x (P.vAt (s.u : ℕ)) (P.vAt (s.v : ℕ)))) : Inv P x t := by
  obtain ⟨hpc, hwu, hacc, huN, hcN, c', u', f', hc', hu', rfl⟩ := hB
  obtain ⟨hcore, hult, hSex, hjle, hw⟩ := hs.2.2.2.1 hpc
  obtain ⟨S, hSsub, hScard, hSacc, hSfnd⟩ := hSex
  have hfnd' : f' = true ↔
      (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ) ∨
        P.step x (P.vAt (s.u : ℕ)) (P.vAt (s.v : ℕ))) := hfnd
  have hvu : P.vAt (s.u : ℕ) ∈ RS P x (s.i : ℕ) := by
    rw [← hwu]
    exact Rle_mono (P.step x) P.st hjle hw
  have hnot : P.vAt (s.u : ℕ) ∉ S := by
    intro hmem
    obtain ⟨-, hlt⟩ := hSsub hmem
    rw [P.idx_vAt huN] at hlt
    omega
  refine inv_mk2 P x _ rfl hcore (by show (u' : ℕ) ≤ P.N; omega) ?_
  refine ⟨insert (P.vAt (s.u : ℕ)) S, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rcases hy with rfl | hy
    · exact ⟨hvu, by show P.idx (P.vAt (s.u : ℕ)) < (u' : ℕ); rw [P.idx_vAt huN]; omega⟩
    · obtain ⟨h1, h2⟩ := hSsub hy
      exact ⟨h1, by show P.idx y < (u' : ℕ); omega⟩
  · rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _), hScard]
    show (s.c : ℕ) + 1 = (c' : ℕ)
    omega
  · intro y hy
    rcases hy with rfl | hy
    · rw [← hwu]; exact hacc
    · exact hSacc y hy
  · show f' = true ↔ ∃ y ∈ insert (P.vAt (s.u : ℕ)) S,
      (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ)))
    rw [hfnd']
    constructor
    · rintro (h1 | h1 | h1)
      · obtain ⟨y, hy, hy2⟩ := hSfnd.mp h1
        exact ⟨y, Or.inr hy, hy2⟩
      · exact ⟨P.vAt (s.u : ℕ), Or.inl rfl, Or.inl h1⟩
      · exact ⟨P.vAt (s.u : ℕ), Or.inl rfl, Or.inr h1⟩
    · rintro ⟨y, (rfl | hy), hy2⟩
      · exact Or.inr hy2
      · exact Or.inl (hSfnd.mpr ⟨y, hy, hy2⟩)

