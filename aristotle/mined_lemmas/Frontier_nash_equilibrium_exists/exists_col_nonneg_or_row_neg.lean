import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to be the very first command in a file, so the header comment
above is placed immediately after it.)
-/

open scoped BigOperators

namespace Frontier

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure strategy `a`, viewed as a (degenerate) mixed strategy. -/

theorem exists_col_nonneg_or_row_neg [Nonempty M] (A : M → N → ℝ) :
    (∃ p ∈ stdSimplex ℝ M, ∀ n, 0 ≤ colPayoff A p n) ∨
      (∃ q ∈ stdSimplex ℝ N, ∀ m, rowPayoff A q m < 0) := by
  by_cases hcase : ∃ p ∈ stdSimplex ℝ M, ∀ n, 0 ≤ colPayoff A p n
  · exact Or.inl hcase
  right
  push_neg at hcase
  -- the linear map sending a mixed row strategy to its vector of payoffs against pure columns
  let L : (M → ℝ) →ₗ[ℝ] (N → ℝ) :=
    { toFun := fun p => colPayoff A p
      map_add' := by
        intro p p'
        funext n
        simp only [colPayoff, Pi.add_apply, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c p
        funext n
        simp only [colPayoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring }
  set K : Set (N → ℝ) := L '' (stdSimplex ℝ M) with hKdef
  have hKc : IsCompact K :=
    (isCompact_stdSimplex M).image (continuous_pi fun n => continuous_colPayoff A n)
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ M).linear_image L
  set T : Set (N → ℝ) := Set.univ.pi fun _ : N => Set.Ici (0 : ℝ) with hTdef
  have hTconv : Convex ℝ T := convex_pi fun n _ => convex_Ici 0
  have hTclosed : IsClosed T := isClosed_set_pi fun n _ => isClosed_Ici
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro y ⟨p, hp, rfl⟩ hyT
    obtain ⟨n, hn⟩ := hcase p hp
    have : (0 : ℝ) ≤ colPayoff A p n := by
      simpa using (Set.mem_univ_pi.1 hyT n)
    linarith
  obtain ⟨f, u, v, hfK, huv, hfT⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKc hTconv hTclosed hdisj
  set c : N → ℝ := fun n => f (Pi.single n 1 : N → ℝ) with hc
  have hf0 : f 0 = 0 := map_zero f
  have hv0 : v < 0 := by
    have h0T : (0 : N → ℝ) ∈ T := by
      refine Set.mem_univ_pi.2 fun n => ?_
      simp
    have := hfT 0 h0T
    rwa [hf0] at this
  have hcnn : ∀ n, 0 ≤ c n := by
    intro n
    by_contra hneg
    push_neg at hneg
    set t : ℝ := (v - 1) / c n with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg (by linarith) hneg
    have hmem : t • (Pi.single n 1 : N → ℝ) ∈ T := by
      refine Set.mem_univ_pi.2 fun n' => ?_
      by_cases h : n = n' <;> simp [h, htpos.le]
    have := hfT _ hmem
    rw [map_smul] at this
    have hcn : t * c n = v - 1 := by
      have hne0 : c n ≠ 0 := ne_of_lt hneg
      rw [ht]
      exact div_mul_cancel₀ _ hne0
    simp only [smul_eq_mul] at this
    rw [hcn] at this
    linarith
  have hfy : ∀ y : N → ℝ, f y = ∑ n, y n * c n := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hsingle : (Pi.single n (y n) : N → ℝ) = y n • (Pi.single n 1 : N → ℝ) := by
      funext n'
      by_cases h : n = n' <;> simp [Pi.single_apply, h]
    rw [hsingle, map_smul]
    simp [hc]
  -- the pure strategies of the row player give points of `K`
  have hpure : ∀ m : M, (fun n => A m n) ∈ K := by
    intro m
    refine ⟨fun m' => if m = m' then 1 else 0, ite_eq_mem_stdSimplex ℝ m, ?_⟩
    funext n
    exact colPayoff_pureStrat A m n
  have hnegrow : ∀ m : M, ∑ n, A m n * c n < 0 := by
    intro m
    have h1 := hfK _ (hpure m)
    rw [hfy] at h1
    linarith
  have hSpos : 0 < ∑ n, c n := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun n _ => hcnn n) with h | h
    · exact h
    · exfalso
      have hzero : ∀ n, c n = 0 := by
        intro n
        have := (Finset.sum_eq_zero_iff_of_nonneg fun n _ => hcnn n).1 h.symm n (Finset.mem_univ n)
        exact this
      have := hnegrow (Classical.arbitrary M)
      rw [Finset.sum_congr rfl fun n _ => by rw [hzero n, mul_zero]] at this
      simp at this
  refine ⟨fun n => c n / ∑ n', c n', ⟨fun n => div_nonneg (hcnn n) hSpos.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hSpos)]
  · intro m
    have hrow : rowPayoff A (fun n => c n / ∑ n', c n') m = (∑ n, A m n * c n) / ∑ n', c n' := by
      simp only [rowPayoff, Finset.sum_div]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hrow]
    exact div_neg_of_neg_of_pos (hnegrow m) hSpos

/-- The row player has an optimal (maximin) mixed strategy. -/
