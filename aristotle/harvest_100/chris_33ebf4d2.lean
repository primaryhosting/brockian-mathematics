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
def HasAP {α : Type*} (c : ℕ → α) (k N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ d < N ∧ a + k * d < N ∧ ∀ i < k, c (a + i * d) = c a

/-- `Fan c k s N` : there are `s` monochromatic arithmetic progressions of length `k`,
with pairwise distinct colors, all *focused* at a common point `f < N` (i.e. the next term
of each progression is `f`), none of them having the color of `f`. -/
def Fan {α : Type*} (c : ℕ → α) (k s N : ℕ) : Prop :=
  ∃ (f : ℕ) (a d : ℕ → ℕ), f < N ∧
    (∀ j < s, 0 < d j ∧ d j < N ∧ a j + k * d j = f ∧ ∀ i < k, c (a j + i * d j) = c (a j)) ∧
    (∀ j₁ < s, ∀ j₂ < s, j₁ ≠ j₂ → c (a j₁) ≠ c (a j₂)) ∧
    (∀ j < s, c (a j) ≠ c f)

/-- `VDWBound k r` : there is a window size `N` such that every `r`-coloring of `ℕ` has a
monochromatic arithmetic progression of length `k` inside `[0, N)`. -/
def VDWBound (k r : ℕ) : Prop := ∃ N : ℕ, ∀ c : ℕ → Fin r, HasAP c k N

theorem HasAP.mono {α : Type*} {c : ℕ → α} {k N N' : ℕ} (h : HasAP c k N) (hN : N ≤ N') :
    HasAP c k N' := by
  obtain ⟨a, d, h1, h2, h3, h4⟩ := h
  exact ⟨a, d, h1, lt_of_lt_of_le h2 hN, lt_of_lt_of_le h3 hN, h4⟩

theorem Fan.mono {α : Type*} {c : ℕ → α} {k s N N' : ℕ} (h : Fan c k s N) (hN : N ≤ N') :
    Fan c k s N' := by
  obtain ⟨f, a, d, hf, h1, h2, h3⟩ := h
  refine ⟨f, a, d, lt_of_lt_of_le hf hN, fun j hj => ?_, h2, h3⟩
  obtain ⟨p1, p2, p3, p4⟩ := h1 j hj
  exact ⟨p1, lt_of_lt_of_le p2 hN, p3, p4⟩

theorem vdw_zero (r : ℕ) : VDWBound 0 r :=
  ⟨2, fun _ => ⟨0, 1, by norm_num, by norm_num, by norm_num, by omega⟩⟩

/-- A fan of size `0` exists trivially. -/
theorem fan_zero (k r : ℕ) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, HasAP c (k + 1) N ∨ Fan c k 0 N := by
  refine ⟨1, fun c => Or.inr ⟨0, fun _ => 0, fun _ => 0, by norm_num, ?_, ?_, ?_⟩⟩ <;> omega

/-- The inductive step for fans: given van der Waerden for progressions of length `k` and
any number of colors, a fan of size `s` can be upgraded to a fan of size `s + 1`, unless a
monochromatic progression of length `k + 1` appears. -/
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

theorem fan_all {k r : ℕ} (hW : ∀ m, VDWBound k m) (s : ℕ) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, HasAP c (k + 1) N ∨ Fan c k s N := by
  induction s with
  | zero => exact fan_zero k r
  | succ n ih => exact fan_step hW ih

/-- A fan with `r` pairwise distinctly colored progressions is impossible for an
`r`-coloring: the focus supplies an `(r+1)`-st color. -/
theorem fan_card {k r N : ℕ} {c : ℕ → Fin r} (h : Fan c k r N) : False := by
  obtain ⟨f, a, d, hf, hAPs, hdist, hfd⟩ := h
  set g : Fin (r + 1) → Fin r := fun j => if h : (j : ℕ) < r then c (a j) else c f with hg
  have hinj : Function.Injective g := by
    intro x y hxy
    simp only [hg] at hxy
    by_cases hx : (x : ℕ) < r <;> by_cases hy : (y : ℕ) < r <;>
      simp only [hx, hy, dif_pos, dif_neg, not_false_iff] at hxy
    · by_contra hne
      exact hdist x hx y hy (fun hc => hne (Fin.ext hc)) hxy
    · exact absurd hxy (hfd x hx)
    · exact absurd hxy.symm (hfd y hy)
    · have : (x : ℕ) = y := by omega
      exact Fin.ext this
  have hle := Fintype.card_le_of_injective g hinj
  simp at hle

theorem vdw_succ {k : ℕ} (hW : ∀ m, VDWBound k m) (r : ℕ) : VDWBound (k + 1) r := by
  obtain ⟨N, hN⟩ := fan_all (k := k) (r := r) hW r
  refine ⟨N, fun c => ?_⟩
  rcases hN c with h | h
  · exact h
  · exact absurd h (fun hh => fan_card hh)

/-- The finitary van der Waerden theorem: for every length `k` and number of colors `r`
there is an `N` such that every `r`-coloring of `ℕ` has a monochromatic arithmetic
progression of length `k` within `[0, N)`. -/
theorem vdw_bound (k r : ℕ) : VDWBound k r := by
  induction k generalizing r with
  | zero => exact vdw_zero r
  | succ n ih => exact vdw_succ (fun m => ih m) r

/-- **Van der Waerden's theorem.** For any coloring of `ℕ` by finitely many colors and any
`k`, there is a monochromatic arithmetic progression of length `k`: a starting point `a`
and a positive common difference `d` such that `a, a + d, …, a + (k-1) * d` all get the
same color. Since `k` is arbitrary, the monochromatic progressions are arbitrarily long. -/
theorem van_der_waerden {α : Type*} [Finite α] (c : ℕ → α) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, c (a + i * d) = c a := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  obtain ⟨N, hN⟩ := vdw_bound k n
  obtain ⟨a, d, hd, -, -, hcol⟩ := hN (fun m => e (c m))
  exact ⟨a, d, hd, fun i hi => e.injective (hcol i hi)⟩

end Math2

