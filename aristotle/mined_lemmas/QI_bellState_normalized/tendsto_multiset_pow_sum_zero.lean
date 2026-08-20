import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

theorem tendsto_multiset_pow_sum_zero {S : Multiset ℝ} {a : ℝ} (ha : 0 < a)
    (h : ∀ x ∈ S, 0 ≤ x ∧ x < a) :
    Filter.Tendsto (fun p : ℕ => (S.map (fun s => (s / a) ^ p)).sum) Filter.atTop (nhds 0) := by
  revert h
  induction S using Multiset.induction_on with
  | empty => intro _; simp
  | cons b S ih =>
      intro h
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have hb := h b (Multiset.mem_cons_self b S)
      have h1 : Filter.Tendsto (fun p : ℕ => (b / a) ^ p) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb.1 ha.le) ((div_lt_one ha).2 hb.2)
      have h2 := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      simpa using h1.add h2

