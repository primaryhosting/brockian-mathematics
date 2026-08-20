import Mathlib
namespace Brockian.Schur

/-- Bound function for the Ramsey-type induction: `fR k` many integers suffice when the
    differences take at most `k` colours. -/

theorem schur (r : ℕ) (hr : 0 < r) :
    ∃ N : ℕ, 0 < N ∧ ∀ c : ℕ → Fin r,
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≤ N ∧ y ≤ N ∧ z ≤ N ∧
        x + y = z ∧ c x = c y ∧ c y = c z := by
  refine ⟨fR r, fR_pos r, ?_⟩
  intro c
  obtain ⟨a, ha, b, hb, d, hd, hab, hbd, h1, h2⟩ :=
    key r c r Finset.univ (by simp) (Finset.range (fR r)) (by simp)
      (fun a _ b _ _ => Finset.mem_univ _)
  simp only [Finset.mem_range] at ha hb hd
  refine ⟨b - a, d - b, d - a, by omega, by omega, by omega, by omega, by omega, by omega, h1, h2⟩

end Brockian.Schur

