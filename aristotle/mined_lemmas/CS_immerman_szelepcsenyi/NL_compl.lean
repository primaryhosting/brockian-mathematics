import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


theorem NL_compl {L : Lang} (h : NL L) : NL (fun n x => ¬ L n x) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨9 * k + 21, ?_⟩
  intro n
  obtain ⟨M, hcard, hM⟩ := hk n
  obtain ⟨M', hcard', hM'⟩ := exists_complement_mach M
  refine ⟨M', ?_, ?_⟩
  · -- the polynomial bound
    have hb : 2 ≤ n + 2 := by omega
    have h1 : 1 ≤ (n + 2) ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : (2 : ℕ) ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left hb 2
    have h3 : Fintype.card M.V + 2 ≤ (n + 2) ^ (k + 2) := by
      have : (n + 2) ^ (k + 2) = (n + 2) ^ k * (n + 2) ^ 2 := by ring
      rw [this]
      have h4 : (n + 2) ^ k * 4 ≤ (n + 2) ^ k * (n + 2) ^ 2 :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have h5 : (Fintype.card M.V + 2) ^ 9 ≤ ((n + 2) ^ (k + 2)) ^ 9 :=
      Nat.pow_le_pow_left h3 9
    have h6 : (6 : ℕ) ≤ (n + 2) ^ 3 := by
      have : (2 : ℕ) ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left hb 3
      omega
    have h7 : 6 * (Fintype.card M.V + 2) ^ 9 ≤ (n + 2) ^ 3 * ((n + 2) ^ (k + 2)) ^ 9 :=
      Nat.mul_le_mul h6 h5
    have h8 : (n + 2) ^ 3 * ((n + 2) ^ (k + 2)) ^ 9 = (n + 2) ^ (9 * k + 21) := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    omega
  · intro x
    show ¬ L n x ↔ M'.Accepts x
    rw [hM' x, hM x]

/-- **Immerman–Szelepcsényi**: nondeterministic logarithmic space is closed under
complementation, `NL = coNL`. -/
