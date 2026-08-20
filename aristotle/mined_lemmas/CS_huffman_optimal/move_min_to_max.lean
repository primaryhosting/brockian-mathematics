import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma move_min_to_max (s : Multiset (ℝ × ℕ)) (a : ℝ) (M : ℕ)
    (ha : a ∈ s.map Prod.fst) (hamin : ∀ x ∈ s.map Prod.fst, a ≤ x)
    (hMmem : M ∈ s.map Prod.snd) (hMmax : ∀ y ∈ s.map Prod.snd, y ≤ M) :
    ∃ s' : Multiset (ℝ × ℕ), (a, M) ∈ s' ∧ s'.map Prod.fst = s.map Prod.fst ∧
      s'.map Prod.snd = s.map Prod.snd ∧ mcost s' ≤ mcost s := by
  obtain ⟨pa, hpa, hpa1⟩ := Multiset.mem_map.mp ha
  obtain ⟨pm, hpm, hpm2⟩ := Multiset.mem_map.mp hMmem
  by_cases h : pa.2 = M
  · refine ⟨s, ?_, rfl, rfl, le_rfl⟩
    have : pa = (a, M) := Prod.ext hpa1 h
    exact this ▸ hpa
  · have hne : pm ≠ pa := by
      intro hh
      exact h (by rw [← hh, hpm2])
    have hpm' : pm ∈ s.erase pa := (Multiset.mem_erase_of_ne hne).mpr hpm
    have hs : s = pa ::ₘ pm ::ₘ (s.erase pa).erase pm := by
      rw [Multiset.cons_erase hpm', Multiset.cons_erase hpa]
    set R := (s.erase pa).erase pm with hR
    have hpa2le : (pa.2 : ℝ) ≤ (M : ℝ) := by
      have := hMmax pa.2 (Multiset.mem_map_of_mem _ hpa)
      exact_mod_cast this
    have hple : a ≤ pm.1 := hamin pm.1 (Multiset.mem_map_of_mem _ hpm)
    refine ⟨(a, M) ::ₘ (pm.1, pa.2) ::ₘ R, Multiset.mem_cons_self _ _, ?_, ?_, ?_⟩
    · conv_rhs => rw [hs]
      simp [hpa1]
    · conv_rhs => rw [hs]
      simp [hpm2, Multiset.cons_swap]
    · conv_rhs => rw [hs]
      simp only [mcost_cons]
      rw [hpa1, hpm2]
      nlinarith [hpa2le, hple]

/-- If a unique codeword has maximal length `M`, then the Kraft sum has slack at least
`2 ^ (-M)`. -/
