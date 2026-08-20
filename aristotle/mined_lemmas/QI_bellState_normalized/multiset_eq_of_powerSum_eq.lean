import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

theorem multiset_eq_of_powerSum_eq {S T : Multiset ℝ} (hS : ∀ x ∈ S, 0 < x)
    (hT : ∀ x ∈ T, 0 < x)
    (h : ∀ p : ℕ, 1 ≤ p → (S.map (· ^ p)).sum = (T.map (· ^ p)).sum) : S = T := by
  classical
  generalize hN : S.card + T.card = N
  induction N using Nat.strong_induction_on generalizing S T with
  | _ N IH =>
    by_cases hST : S + T = 0
    · rw [AddLeftCancelMonoid.add_eq_zero] at hST
      rw [hST.1, hST.2]
    · obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hST
      have hUne : (S + T).toFinset.Nonempty := ⟨z, Multiset.mem_toFinset.2 hz⟩
      set a := (S + T).toFinset.max' hUne with ha_def
      have ha_mem : a ∈ S + T := Multiset.mem_toFinset.1 ((S + T).toFinset.max'_mem hUne)
      have hapos : 0 < a := by
        rcases Multiset.mem_add.1 ha_mem with h' | h'
        · exact hS a h'
        · exact hT a h'
      have hle : ∀ x ∈ S + T, x ≤ a := fun x hx =>
        (S + T).toFinset.le_max' x (Multiset.mem_toFinset.2 hx)
      -- split off the copies of `a`
      set cS := S.count a with hcS
      set cT := T.count a with hcT
      set S' := S.filter (fun x => ¬ x = a) with hS'
      set T' := T.filter (fun x => ¬ x = a) with hT'
      have hSsplit : Multiset.replicate cS a + S' = S := by
        rw [hS', hcS, ← Multiset.filter_eq' S a]
        exact Multiset.filter_add_not _ S
      have hTsplit : Multiset.replicate cT a + T' = T := by
        rw [hT', hcT, ← Multiset.filter_eq' T a]
        exact Multiset.filter_add_not _ T
      have hS'pos : ∀ x ∈ S', 0 < x := fun x hx => hS x (Multiset.mem_of_mem_filter hx)
      have hT'pos : ∀ x ∈ T', 0 < x := fun x hx => hT x (Multiset.mem_of_mem_filter hx)
      have hS'lt : ∀ x ∈ S', 0 ≤ x ∧ x < a := by
        intro x hx
        refine ⟨(hS'pos x hx).le, lt_of_le_of_ne (hle x (Multiset.mem_add.2 (Or.inl
          (Multiset.mem_of_mem_filter hx)))) ?_⟩
        exact (Multiset.mem_filter.1 hx).2
      have hT'lt : ∀ x ∈ T', 0 ≤ x ∧ x < a := by
        intro x hx
        refine ⟨(hT'pos x hx).le, lt_of_le_of_ne (hle x (Multiset.mem_add.2 (Or.inr
          (Multiset.mem_of_mem_filter hx)))) ?_⟩
        exact (Multiset.mem_filter.1 hx).2
      -- power sums split
      have hsplitS : ∀ p : ℕ, (S.map (· ^ p)).sum = cS * a ^ p + (S'.map (· ^ p)).sum := by
        intro p
        rw [← hSsplit]
        simp [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
      have hsplitT : ∀ p : ℕ, (T.map (· ^ p)).sum = cT * a ^ p + (T'.map (· ^ p)).sum := by
        intro p
        rw [← hTsplit]
        simp [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
      -- the counts agree
      have hcount : cS = cT := by
        have key : ∀ p : ℕ, 1 ≤ p →
            (cS : ℝ) + (S'.map (fun s => (s / a) ^ p)).sum
              = (cT : ℝ) + (T'.map (fun s => (s / a) ^ p)).sum := by
          intro p hp
          have hap : (a : ℝ) ^ p ≠ 0 := by positivity
          have := h p hp
          rw [hsplitS p, hsplitT p] at this
          rw [multiset_sum_map_div_pow, multiset_sum_map_div_pow]
          field_simp
          linarith [this]
        have t1 : Filter.Tendsto
            (fun p : ℕ => (cS : ℝ) + (S'.map (fun s => (s / a) ^ p)).sum)
            Filter.atTop (nhds (cS : ℝ)) := by
          simpa using tendsto_const_nhds.add (tendsto_multiset_pow_sum_zero hapos hS'lt)
        have t2 : Filter.Tendsto
            (fun p : ℕ => (cT : ℝ) + (T'.map (fun s => (s / a) ^ p)).sum)
            Filter.atTop (nhds (cT : ℝ)) := by
          simpa using tendsto_const_nhds.add (tendsto_multiset_pow_sum_zero hapos hT'lt)
        have t1' : Filter.Tendsto
            (fun p : ℕ => (cT : ℝ) + (T'.map (fun s => (s / a) ^ p)).sum)
            Filter.atTop (nhds (cS : ℝ)) := by
          refine t1.congr' ?_
          filter_upwards [Filter.eventually_ge_atTop 1] with p hp using key p hp
        have : (cS : ℝ) = (cT : ℝ) := tendsto_nhds_unique t1' t2
        exact_mod_cast this
      -- the counts are positive
      have hcSpos : 1 ≤ cS := by
        have : 0 < Multiset.count a (S + T) := Multiset.count_pos.2 ha_mem
        rw [Multiset.count_add, ← hcS, ← hcT, ← hcount] at this
        omega
      -- apply the induction hypothesis
      have hcard : S'.card + T'.card < N := by
        have h1 : S'.card + cS = S.card := by
          rw [← hSsplit]; simp [Multiset.card_add, Multiset.card_replicate]; omega
        have h2 : T'.card + cT = T.card := by
          rw [← hTsplit]; simp [Multiset.card_add, Multiset.card_replicate]; omega
        omega
      have hpow : ∀ p : ℕ, 1 ≤ p → (S'.map (· ^ p)).sum = (T'.map (· ^ p)).sum := by
        intro p hp
        have := h p hp
        rw [hsplitS p, hsplitT p, hcount] at this
        linarith
      have := IH (S'.card + T'.card) hcard hS'pos hT'pos hpow rfl
      rw [← hSsplit, ← hTsplit, this, hcount]

/-! ### The reduced density matrix -/

/-- The reduced density matrix of `psi` on the first factor. -/
