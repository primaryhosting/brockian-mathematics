import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem finite_of_erdos (h : ErdosDiscrepancyStatement) : FiniteErdosStatement := by
  classical
  intro C
  by_contra hcon
  push_neg at hcon
  -- for each `N`, a `±1` sequence with discrepancy `≤ C` inside `{1, …, N}`
  choose g hg1 hg2 using hcon
  let u : Ultrafilter ℕ := Filter.hyperfilter ℕ
  -- the ultrafilter limit of the sequences `g N`
  let f : ℕ → ℤ := fun k => if {N | g N k = 1} ∈ u then 1 else -1
  have hfval : ∀ k, f k = if {N | g N k = 1} ∈ u then 1 else -1 := fun _ => rfl
  have hf : IsPMOne f := by
    intro k _
    rw [hfval]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- each coordinate of `f` is the value of `g N` for `u`-most `N`
  have hA : ∀ k, 1 ≤ k → {N | g N k = f k} ∈ (u : Filter ℕ) := by
    intro k hk
    by_cases hmem : {N | g N k = 1} ∈ u
    · have hfk : f k = 1 := by rw [hfval]; exact if_pos hmem
      filter_upwards [Ultrafilter.mem_coe.mpr hmem] with N hN
      show g N k = f k
      rw [hfk]; exact hN
    · have hfk : f k = -1 := by rw [hfval]; exact if_neg hmem
      have hc : {N | g N k = 1}ᶜ ∈ (u : Filter ℕ) :=
        Ultrafilter.mem_coe.mpr (Ultrafilter.compl_mem_iff_notMem.mpr hmem)
      filter_upwards [hc] with N hN
      show g N k = f k
      rcases hg1 N k hk with hv | hv
      · exact absurd hv hN
      · rw [hfk]; exact hv
  -- hence for `u`-most `N` the sequence `g N` agrees with `f` on all of `{1, …, M}`
  have agree : ∀ M : ℕ, {N | ∀ k, 1 ≤ k → k ≤ M → g N k = f k} ∈ (u : Filter ℕ) := by
    intro M
    induction M with
    | zero =>
        filter_upwards with N k hk1 hk2
        exact absurd (hk1.trans hk2) (by decide)
    | succ m ih =>
        filter_upwards [ih, hA (m + 1) (Nat.le_add_left 1 m)] with N h1 h2 k hk1 hk2
        rcases Nat.lt_or_ge k (m + 1) with hlt | hge
        · exact h1 k hk1 (Nat.lt_succ_iff.mp hlt)
        · have : k = m + 1 := le_antisymm hk2 hge
          subst this; exact h2
  -- apply the infinite statement to the limit sequence `f`
  obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
  have hbig : {N : ℕ | n * d ≤ N} ∈ (u : Filter ℕ) := by
    refine Filter.hyperfilter_le_cofinite ?_
    rw [Filter.mem_cofinite]
    exact Set.Finite.subset (Set.finite_Iio (n * d)) fun x hx => by simpa using hx
  obtain ⟨N, hN1, hN2⟩ := Filter.nonempty_of_mem (Filter.inter_mem (agree (n * d)) hbig)
  have hsum : homogSum f d n = homogSum (g N) d n :=
    homogSum_congr hd fun k hk1 hk2 => (hN1 k hk1 hk2).symm
  have hle : (homogSum (g N) d n).natAbs ≤ C := hg2 N d n hd hn hN2
  omega

/-- **Lean-checked reduction.** The Erdős discrepancy statement is equivalent to its
finitary form. -/
