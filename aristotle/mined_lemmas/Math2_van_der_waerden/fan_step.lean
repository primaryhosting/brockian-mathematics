/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Van Der Waerden

Category: Frontier Math

Target: `Math2.van_der_waerden`

Provenance: Aristotle theorem prover (Harmonic)

Any finite coloring of `ℕ` has arbitrarily long monochromatic arithmetic progressions.

The proof is the classical "color focusing" (Graham–Rothschild) double induction:
an outer induction on the length `k` of the progression, and, inside it, an induction on
the number `s` of *focused* progressions with pairwise distinct colors that can be found
in a sufficiently long window.
-/

set_option autoImplicit false

namespace Math2

/-- `HasAP c k N` : the coloring `c` has a monochromatic arithmetic progression of
length `k` (with positive common difference `d < N`) such that even the "next" term
`a + k * d` lies below `N`. -/

theorem fan_step {k r s : ℕ} (hW : ∀ m, VDWBound k m)
    (hs : ∃ N : ℕ, ∀ c : ℕ → Fin r, HasAP c (k + 1) N ∨ Fan c k s N) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, HasAP c (k + 1) N ∨ Fan c k (s + 1) N := by
  obtain ⟨Ns0, hNs0⟩ := hs
  -- we may assume the window size for fans of size `s` is positive
  obtain ⟨Ns, hNspos, hNs⟩ :
      ∃ Ns : ℕ, 0 < Ns ∧ ∀ c : ℕ → Fin r, HasAP c (k + 1) Ns ∨ Fan c k s Ns := by
    refine ⟨Ns0 + 1, by omega, fun c => ?_⟩
    rcases hNs0 c with h | h
    · exact Or.inl (h.mono (by omega))
    · exact Or.inr (h.mono (by omega))
  -- van der Waerden of length `k` for colorings of blocks of length `Ns`
  obtain ⟨L, hL⟩ := hW (r ^ Ns)
  have hcard : Fintype.card (Fin Ns → Fin r) = r ^ Ns := by simp
  let e : (Fin Ns → Fin r) ≃ Fin (r ^ Ns) := Fintype.equivFinOfCardEq hcard
  refine ⟨(2 * L + 1) * Ns, fun c => ?_⟩
  obtain ⟨b, ee, hee0, heeL, hbL', hCeq⟩ := hL (fun t => e (fun z => c (t * Ns + z)))
  -- the blocks `b`, `b + ee`, ..., `b + (k-1) * ee` are colored identically
  have key : ∀ i < k, ∀ j < Ns, c ((b + i * ee) * Ns + j) = c (b * Ns + j) := by
    intro i hi j hj
    have h2 : (fun (z : Fin Ns) => c ((b + i * ee) * Ns + z))
        = fun (z : Fin Ns) => c (b * Ns + z) := e.injective (hCeq i hi)
    exact congrFun h2 ⟨j, hj⟩
  have hmul : ∀ x y : ℕ, x ≤ y → x * Ns ≤ y * Ns := fun x y h => Nat.mul_le_mul_right Ns h
  rcases hNs (fun n => c (b * Ns + n)) with hAP | hFan
  · -- a monochromatic progression of length `k + 1` already lives inside block `b`
    obtain ⟨a, d, hd0, hdN, hlt, hcol⟩ := hAP
    left
    refine ⟨b * Ns + a, d, hd0, ?_, ?_, ?_⟩
    · have : Ns ≤ (2 * L + 1) * Ns := by nlinarith
      omega
    · have h1 : (b + 1) * Ns = b * Ns + Ns := by ring
      have h2 : (b + 1) * Ns ≤ (2 * L + 1) * Ns := hmul _ _ (by omega)
      have h3 : b * Ns + a + (k + 1) * d = b * Ns + (a + (k + 1) * d) := by ring
      linarith
    · intro i hi
      have h := hcol i hi
      simp only at h
      rw [show b * Ns + a + i * d = b * Ns + (a + i * d) by ring]
      exact h
  · -- block `b` carries a fan of size `s`; stretch it across the blocks
    obtain ⟨f, a, d, hf, hAPs, hdist, hfd⟩ := hFan
    simp only at hAPs hdist hfd
    set A : ℕ → ℕ := fun j => if j = s then b * Ns + f else b * Ns + a j with hA
    set D : ℕ → ℕ := fun j => if j = s then ee * Ns else d j + ee * Ns with hD
    set F : ℕ := b * Ns + f + k * (ee * Ns) with hF
    have haf : ∀ j < s, ∀ i ≤ k, a j + i * d j ≤ f := by
      intro j hj i hi
      obtain ⟨-, -, he, -⟩ := hAPs j hj
      have : i * d j ≤ k * d j := Nat.mul_le_mul_right _ hi
      omega
    have hD0 : ∀ j < s + 1, 0 < D j := by
      intro j hj
      by_cases h : j = s
      · simp only [hD, h, if_pos]
        exact Nat.mul_pos hee0 hNspos
      · have hjs : j < s := by omega
        obtain ⟨h1, -, -, -⟩ := hAPs j hjs
        simp only [hD, h, if_false]
        omega
    have hDlt : ∀ j < s + 1, D j < (L + 1) * Ns := by
      intro j hj
      have hLNs : L * Ns ≤ (L + 1) * Ns := hmul _ _ (by omega)
      have hee : ee * Ns < L * Ns := (Nat.mul_lt_mul_right hNspos).mpr heeL
      by_cases h : j = s
      · simp only [hD, h, if_pos]; linarith
      · have hjs : j < s := by omega
        obtain ⟨-, h2, -, -⟩ := hAPs j hjs
        have : (L + 1) * Ns = L * Ns + Ns := by ring
        simp only [hD, h, if_false]
        linarith
    have hfocus : ∀ j < s + 1, A j + k * D j = F := by
      intro j hj
      by_cases h : j = s
      · simp only [hA, hD, hF, h, if_pos]
      · have hjs : j < s := by omega
        obtain ⟨-, -, he, -⟩ := hAPs j hjs
        simp only [hA, hD, h, if_false, hF]
        rw [show b * Ns + a j + k * (d j + ee * Ns)
          = b * Ns + (a j + k * d j) + k * (ee * Ns) by ring, he]
    have hcolA : ∀ j < s + 1, ∀ i < k, c (A j + i * D j) = c (A j) := by
      intro j hj i hi
      by_cases h : j = s
      · simp only [hA, hD, h, if_pos]
        rw [show b * Ns + f + i * (ee * Ns) = (b + i * ee) * Ns + f by ring]
        exact key i hi f hf
      · have hjs : j < s := by omega
        obtain ⟨-, -, he, hc⟩ := hAPs j hjs
        have hlt : a j + i * d j < Ns := lt_of_le_of_lt (haf j hjs i (le_of_lt hi)) hf
        simp only [hA, hD, h, if_false]
        rw [show b * Ns + a j + i * (d j + ee * Ns) = (b + i * ee) * Ns + (a j + i * d j) by ring,
          key i hi _ hlt]
        exact hc i hi
    have hFlt : F < L * Ns := by
      have h1 : F = (b + k * ee) * Ns + f := by rw [hF]; ring
      have h2 : (b + k * ee + 1) * Ns = (b + k * ee) * Ns + Ns := by ring
      have h3 : (b + k * ee + 1) * Ns ≤ L * Ns := hmul _ _ (by omega)
      linarith
    have hsum : L * Ns + (L + 1) * Ns = (2 * L + 1) * Ns := by ring
    by_cases hex : ∃ j < s + 1, c F = c (A j)
    · -- the new focus repeats one of the colors: a progression of length `k + 1`
      obtain ⟨j, hj, hcF⟩ := hex
      left
      refine ⟨A j, D j, hD0 j hj, ?_, ?_, ?_⟩
      · linarith [hDlt j hj, Nat.zero_le (L * Ns)]
      · rw [show A j + (k + 1) * D j = (A j + k * D j) + D j by ring, hfocus j hj]
        linarith [hDlt j hj, hFlt]
      · intro i hi
        rcases Nat.lt_or_ge i k with h | h
        · exact hcolA j hj i h
        · have : i = k := by omega
          subst this
          rw [hfocus j hj]
          exact hcF
    · -- otherwise we obtain a fan of size `s + 1`
      right
      push_neg at hex
      refine ⟨F, A, D, ?_, ?_, ?_, ?_⟩
      · linarith [hFlt, hmul L (2 * L + 1) (by omega)]
      · exact fun j hj => ⟨hD0 j hj, by linarith [hDlt j hj, Nat.zero_le (L * Ns)],
          hfocus j hj, hcolA j hj⟩
      · intro j1 hj1 j2 hj2 hne
        by_cases h1 : j1 = s <;> by_cases h2 : j2 = s
        · exact absurd (h1.trans h2.symm) hne
        · have hj2s : j2 < s := by omega
          simp only [hA, h1, h2, if_pos, if_false]
          exact fun hc => hfd j2 hj2s hc.symm
        · have hj1s : j1 < s := by omega
          simp only [hA, h1, h2, if_pos, if_false]
          exact hfd j1 hj1s
        · have hj1s : j1 < s := by omega
          have hj2s : j2 < s := by omega
          simp only [hA, h1, h2, if_false]
          exact hdist j1 hj1s j2 hj2s hne
      · intro j hj
        exact fun hc => hex j hj hc.symm

