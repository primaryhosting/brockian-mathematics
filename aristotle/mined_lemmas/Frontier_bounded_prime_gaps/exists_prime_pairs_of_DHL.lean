import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- The `n`-th prime gap `p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n`. -/

lemma exists_prime_pairs_of_DHL {k : ℕ} (h : DicksonHardyLittlewood k) :
    ∃ B : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B := by
  classical
  obtain ⟨H, hcard, hadm⟩ := exists_admissible k
  refine ⟨H.sup id, fun N => ?_⟩
  obtain ⟨n, hn, hNn⟩ := (h H hcard hadm).exists_gt N
  simp only [Set.mem_setOf_eq] at hn
  have hn' : 1 < (H.filter fun h => Nat.Prime (n + h)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hn'
  rw [Finset.mem_filter] at ha hb
  obtain ⟨haH, hpa⟩ := ha
  obtain ⟨hbH, hpb⟩ := hb
  have hasup : a ≤ H.sup id := Finset.le_sup (f := id) haH
  have hbsup : b ≤ H.sup id := Finset.le_sup (f := id) hbH
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨n + a, n + b, by omega, hpa, hpb, by omega, by omega⟩
  · exact ⟨n + b, n + a, by omega, hpb, hpa, by omega, by omega⟩

end Reduction

/-- **Bounded prime gaps** (Zhang, Maynard), as a Lean-checked reduction: the
Dickson–Hardy–Littlewood hypothesis `DHL[k,2]` for some `k ≥ 2` implies that the `liminf`
of the prime gaps `p_{n+1} - p_n` is finite. -/
