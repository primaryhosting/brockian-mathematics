/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Statement: Any finite coloring of ℕ has arbitrarily long monochromatic APs (van der Waerden).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- `HasAP c m N` says the coloring `c` admits a monochromatic arithmetic progression of
length `m` with positive common difference, contained (together with a little slack) in
`[0, N]`. -/

theorem fan_induction {K : Type} [Finite K] {k : ℕ} (hk : 1 ≤ k) (Wk : VDW k) (s : ℕ) :
    ∃ N : ℕ, ∀ c : ℕ → K, HasAP c (k + 1) N ∨ FanFamily c k s N := by
  induction s with
  | zero =>
    refine ⟨0, fun c => Or.inr ⟨0, fun _ => 0, fun _ => 0, le_rfl, ?_, ?_, ?_, ?_⟩⟩ <;> simp
  | succ s ih =>
    obtain ⟨Ns, hNs⟩ := ih
    set B := Ns + 1 with hBdef
    have hBpos : 0 < B := by omega
    obtain ⟨M, hM⟩ := Wk (Fin B → K)
    refine ⟨(M + 2) * B, fun c => ?_⟩
    obtain ⟨b, e, he, hbM, hblocks⟩ := hM (fun t i => c (t * B + i))
    have hb : b ≤ M := by omega
    have hbB : b * B ≤ M * B := Nat.mul_le_mul_right B hb
    have hMB : (M + 2) * B = M * B + 2 * B := by ring
    -- transfer of colors between blocks with the same pattern
    have key : ∀ i, i < k → ∀ x, x < B → c ((b + i * e) * B + x) = c (b * B + x) := by
      intro i hi x hx
      have h := congrFun (hblocks i hi) (⟨x, hx⟩ : Fin B)
      simpa using h
    rcases hNs (fun x => c (b * B + x)) with hAP | hFan
    · -- a monochromatic AP of length `k+1` inside the block, translated back
      obtain ⟨a, d, hd, hbound, hmono⟩ := hAP
      refine Or.inl ⟨b * B + a, d, hd, ?_, ?_⟩
      · omega
      · intro i hi
        have h1 : b * B + a + i * d = b * B + (a + i * d) := by ring
        rw [h1]
        exact hmono i hi
    · obtain ⟨f, a, d, hfN, hdpos, hfocus, hmonof, hinj⟩ := hFan
      by_cases hcol : ∃ j < s, c (b * B + f) = c (b * B + a j)
      · -- the focus has the color of one of the fans: extend that fan
        obtain ⟨j, hj, hcj⟩ := hcol
        have hfj : a j + k * d j = f := hfocus j hj
        have hdle : d j ≤ k * d j := Nat.le_mul_of_pos_left _ hk
        have hexp : (k + 1) * d j = k * d j + d j := by ring
        refine Or.inl ⟨b * B + a j, d j, hdpos j hj, by omega, ?_⟩
        intro i hi
        rcases Nat.lt_or_ge i k with hik | hik
        · have h1 : b * B + a j + i * d j = b * B + (a j + i * d j) := by ring
          rw [h1]
          exact hmonof j hj i hik
        · have hik' : i = k := by omega
          subst hik'
          have h1 : b * B + a j + i * d j = b * B + f := by rw [← hfj]; ring
          rw [h1]
          exact hcj
      · -- otherwise we get one more fan, focused at the same point
        push_neg at hcol
        refine Or.inr ⟨b * B + f + k * (e * B),
          fun j => if j = s then b * B + f else b * B + a j,
          fun j => if j = s then e * B else d j + e * B, ?_, ?_, ?_, ?_, ?_⟩
        · have hexp : b * B + f + k * (e * B) = (b + k * e) * B + f := by ring
          have hle : (b + k * e) * B ≤ M * B := Nat.mul_le_mul_right B hbM
          omega
        · intro j hj
          by_cases hjs : j = s
          · simp only [hjs, if_true]
            exact Nat.mul_pos he hBpos
          · simp only [if_neg hjs]
            have := hdpos j (by omega)
            omega
        · intro j hj
          by_cases hjs : j = s
          · simp only [hjs, if_true]
          · simp only [if_neg hjs]
            have h1 : b * B + a j + k * (d j + e * B)
                = b * B + (a j + k * d j) + k * (e * B) := by ring
            rw [h1, hfocus j (by omega)]
        · intro j hj i hi
          by_cases hjs : j = s
          · simp only [hjs, if_true]
            have h1 : b * B + f + i * (e * B) = (b + i * e) * B + f := by ring
            rw [h1]
            exact key i hi f (by omega)
          · simp only [if_neg hjs]
            have hjs' : j < s := by omega
            have hfj : a j + k * d j = f := hfocus j hjs'
            have hlt : a j + i * d j < B := by
              have : i * d j ≤ k * d j := Nat.mul_le_mul_right _ (le_of_lt hi)
              omega
            have h1 : b * B + a j + i * (d j + e * B)
                = (b + i * e) * B + (a j + i * d j) := by ring
            rw [h1, key i hi (a j + i * d j) hlt]
            exact hmonof j hjs' i hi
        · intro i hi j hj hij
          by_cases his : i = s <;> by_cases hjs : j = s
          · omega
          · simp only [his, if_true, if_neg hjs] at hij
            exact absurd hij (hcol j (by omega))
          · simp only [hjs, if_true, if_neg his] at hij
            exact absurd hij.symm (hcol i (by omega))
          · simp only [if_neg his, if_neg hjs] at hij
            exact hinj i (by omega) j (by omega) hij

