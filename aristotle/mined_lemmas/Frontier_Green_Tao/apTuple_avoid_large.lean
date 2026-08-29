import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any other
command in a module, including module docstrings, so the mandated header comment appears
immediately after the single `import Mathlib` line.
-/

open scoped BigOperators

namespace Frontier

/-- `PrimeAP k` says that there is an arithmetic progression of length `k` with positive
common difference all of whose terms are prime. -/

lemma apTuple_avoid_large {k p : ℕ} (hp : p.Prime) (hpk : k < p) :
    ∃ n : ℕ, ∀ b ∈ apTuple k, ¬ (p ∣ n + b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set S : Finset (ZMod p) := (Finset.range k).image (fun i => -((i * Nat.factorial k : ℕ) : ZMod p))
    with hS
  have h1 : S.card ≤ k := le_trans (Finset.card_image_le) (by simp)
  have hne : ∃ x : ZMod p, x ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ S := fun x _ => hcon x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card p] at hle
    omega
  obtain ⟨x, hx⟩ := hne
  refine ⟨x.val, ?_⟩
  intro b hb hdvd
  rcases mem_apTuple.mp hb with ⟨i, hi, rfl⟩
  apply hx
  have hz : ((x.val + i * Nat.factorial k : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  push_cast at hz
  rw [ZMod.natCast_val, ZMod.cast_id] at hz
  have : -((i * Nat.factorial k : ℕ) : ZMod p) = x := by push_cast; linear_combination -hz
  rw [hS]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, this⟩

/-- The tuple `{0, W, …, (k-1)W}` with `W = k !` is admissible. -/
