/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Math2

/-- The embedding of `[n] = {0, ..., n-1}` into `Fin n` (for `n > 0`). -/
private def emb (n : ℕ) (hn : 0 < n) (a : ℕ) : Fin n := ⟨a % n, Nat.mod_lt _ hn⟩

private lemma emb_apply_of_lt {n : ℕ} (hn : 0 < n) {a : ℕ} (ha : a < n) :
    (emb n hn a : ℕ) = a := by
  simp [emb, Nat.mod_eq_of_lt ha]

private lemma emb_injOn {n : ℕ} (hn : 0 < n) :
    Set.InjOn (emb n hn) (Finset.range n) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have := congrArg (Fin.val) hab
  rwa [emb_apply_of_lt hn ha, emb_apply_of_lt hn hb] at this

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of
`[n] = {0, 1, ..., n-1}` with `n ≥ 2k` has at most `(n-1).choose (k-1)` members. -/
theorem erdos_ko_rado {n k : ℕ} (F : Finset (Finset ℕ))
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n)
    (huniform : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    F.card ≤ (n - 1).choose (k - 1) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- `n = 0` forces `k = 0` and `F = ∅`
    subst hn0
    have hFempty : F = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro A hA
      obtain ⟨x, hx⟩ := hinter A hA A hA
      have := hsub A hA (Finset.mem_inter.1 hx).1
      simp at this
    simp [hFempty]
  · -- transport the family into `Finset (Fin n)`
    set e := emb n hn0 with he
    have hinj : Set.InjOn e (Finset.range n) := emb_injOn hn0
    have hAinj : ∀ A ∈ F, Set.InjOn e (A : Set ℕ) := by
      intro A hA
      exact hinj.mono (by exact_mod_cast hsub A hA)
    set 𝒜 : Finset (Finset (Fin n)) := F.image (fun A => A.image e) with h𝒜
    have key : ∀ C ∈ F, (C.image e).image (Fin.val) = C := by
      intro C hC
      ext x
      simp only [Finset.mem_image, exists_exists_and_eq_and]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (e y : ℕ) = y := emb_apply_of_lt hn0 (Finset.mem_range.1 (hsub C hC hy))
        rwa [hy']
      · intro hx
        exact ⟨x, hx, emb_apply_of_lt hn0 (Finset.mem_range.1 (hsub C hC hx))⟩
    have hcard : 𝒜.card = F.card := by
      rw [h𝒜, Finset.card_image_of_injOn]
      intro A hA B hB hAB
      simp only at hAB
      have h := congrArg (Finset.image (Fin.val (n := n))) hAB
      rw [key A (Finset.mem_coe.1 hA), key B (Finset.mem_coe.1 hB)] at h
      exact h
    have hsized : (𝒜 : Set (Finset (Fin n))).Sized k := by
      intro s hs
      simp only [h𝒜, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
      obtain ⟨A, hA, rfl⟩ := hs
      rw [Finset.card_image_of_injOn (hAinj A hA), huniform A hA]
    have hint : (𝒜 : Set (Finset (Fin n))).Intersecting := by
      intro s hs t ht
      simp only [h𝒜, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs ht
      obtain ⟨A, hA, rfl⟩ := hs
      obtain ⟨B, hB, rfl⟩ := ht
      obtain ⟨x, hx⟩ := hinter A hA B hB
      rw [Finset.mem_inter] at hx
      intro hdisj
      have h1 : e x ∈ A.image e := Finset.mem_image_of_mem e hx.1
      have h2 : e x ∈ B.image e := Finset.mem_image_of_mem e hx.2
      exact (Finset.disjoint_left.1 hdisj h1) h2
    have hk : k ≤ n / 2 := by omega
    have := Finset.erdos_ko_rado hint hsized hk
    rwa [hcard] at this

end Math2

