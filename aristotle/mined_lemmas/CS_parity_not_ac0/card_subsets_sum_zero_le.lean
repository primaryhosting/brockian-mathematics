import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

lemma card_subsets_sum_zero_le (s : Finset (Fin m)) (z : Fin m → ZMod 3)
    (j₀ : Fin m) (hj₀ : j₀ ∈ s) (hz : z j₀ = 1) :
    2 * ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun U => ∑ j ∈ s ∩ U, z j = 0)).card ≤ 2 ^ m := by
  classical
  set F0 := (Finset.univ : Finset (Finset (Fin m))).filter (fun U => ∑ j ∈ s ∩ U, z j = 0) with hF0
  set F1 := (Finset.univ : Finset (Finset (Fin m))).filter (fun U => ¬ (∑ j ∈ s ∩ U, z j = 0))
    with hF1
  have hsum : F0.card + F1.card = 2 ^ m := by
    rw [hF0, hF1, Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ, Fintype.card_finset]
  have hinj : F0.card ≤ F1.card := by
    refine Finset.card_le_card_of_injOn (fun U => symmDiff U {j₀}) ?_ ?_
    · intro U hU
      simp only [Finset.mem_coe, hF0, Finset.mem_filter, Finset.mem_univ, true_and] at hU
      simp only [Finset.mem_coe, hF1, Finset.mem_filter, Finset.mem_univ, true_and]
      show ¬ (∑ j ∈ s ∩ symmDiff U {j₀}, z j = 0)
      by_cases hjU : j₀ ∈ U
      · have hset : s ∩ symmDiff U {j₀} = (s ∩ U).erase j₀ := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton,
            Finset.mem_erase]
          constructor
          · rintro ⟨his, h⟩
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h2, his, h1⟩
            · exact absurd hjU (h1 ▸ h2)
          · rintro ⟨hne, his, hiU⟩
            exact ⟨his, Or.inl ⟨hiU, hne⟩⟩
        rw [hset]
        have hmem : j₀ ∈ s ∩ U := Finset.mem_inter.mpr ⟨hj₀, hjU⟩
        have := Finset.add_sum_erase _ z hmem
        rw [hU, hz] at this
        intro hc
        rw [hc, add_zero] at this
        exact absurd this.symm (by decide)
      · have hset : s ∩ symmDiff U {j₀} = insert j₀ (s ∩ U) := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton,
            Finset.mem_insert]
          constructor
          · rintro ⟨his, h⟩
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr ⟨his, h1⟩
            · exact Or.inl h1
          · rintro (rfl | ⟨his, hiU⟩)
            · exact ⟨hj₀, Or.inr ⟨rfl, hjU⟩⟩
            · exact ⟨his, Or.inl ⟨hiU, by rintro rfl; exact hjU hiU⟩⟩
        rw [hset, Finset.sum_insert (by simp [hjU]), hU, hz, add_zero]
        decide
    · intro U _ V _ h
      have h' : symmDiff U {j₀} = symmDiff V {j₀} := h
      have h2 : symmDiff (symmDiff U {j₀}) {j₀} = symmDiff (symmDiff V {j₀}) {j₀} := by rw [h']
      simpa [symmDiff_assoc] using h2
  omega

/-- The number of tuples all of whose entries satisfy `P`. -/
