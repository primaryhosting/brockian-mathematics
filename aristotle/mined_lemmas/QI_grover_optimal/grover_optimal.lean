import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The BBBV lower bound for unstructured quantum search

We formalise the Bennett–Bernstein–Brassard–Vazirani hybrid argument: any quantum
algorithm that makes `T` queries to a phase oracle marking an unknown element `x`
of a search space `κ` of size `N`, and that identifies `x` with probability at
least `2/3`, must satisfy `T ≥ √N / 25`.  In particular `T = Ω(√N)`, so Grover's
algorithm, which uses `O(√N)` queries, is optimal up to a constant factor.

The computational model:

* the algorithm works on a finite dimensional Hilbert space `EuclideanSpace ℂ ι`,
  whose basis vectors are indexed by `ι` (query register together with an arbitrary
  workspace);
* `Q x ⊆ ι` is the set of basis vectors on which the oracle for the marked element
  `x` flips the phase; different marked elements flip disjoint sets of basis states
  (a basis state queries at most one index);
* the algorithm alternates arbitrary unitaries `U 0, U 1, …` with oracle calls,
  starting from an arbitrary unit vector `psi0`;
* the answer is read off by measuring: `Ans x ⊆ ι` is the set of basis states on
  which the algorithm outputs `x`, and these sets are pairwise disjoint.
-/

namespace QI

open Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The state space of the algorithm: amplitudes indexed by the basis `ι`. -/
abbrev St (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι

/-- Restriction of a state to the coordinates in `S` (orthogonal projection). -/

theorem grover_optimal
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (N T : ℕ) (hN : Fintype.card κ = N) (hN2 : 2 ≤ N)
    (Q : κ → Finset ι) (hQ : ∀ x y, x ≠ y → Disjoint (Q x) (Q y))
    (Ans : κ → Finset ι) (hAns : ∀ x y, x ≠ y → Disjoint (Ans x) (Ans y))
    (U : ℕ → (St ι ≃ₗᵢ[ℂ] St ι)) (psi0 : St ι) (hpsi0 : ‖psi0‖ = 1)
    (hsucc : ∀ x : κ, (2 : ℝ) / 3 ≤ ‖restrict (Ans x) (run U (Q x) psi0 T)‖ ^ 2) :
    Real.sqrt N / 25 ≤ T := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by norm_num) hN2
  -- the oracle-free run
  set psi : ℕ → St ι := fun t => run U ∅ psi0 t with hpsidef
  have hpsinorm : ∀ t, ‖psi t‖ = 1 := fun t => by rw [hpsidef]; simp [run_norm, hpsi0]
  -- query weights
  set q : κ → ℝ := fun x => ∑ t ∈ Finset.range T, ‖restrict (Q x) (psi t)‖ ^ 2 with hqdef
  have hqnonneg : ∀ x, 0 ≤ q x := by
    intro x; rw [hqdef]; positivity
  have hqsum : ∑ x, q x ≤ T := by
    rw [hqdef]
    calc ∑ x : κ, ∑ t ∈ Finset.range T, ‖restrict (Q x) (psi t)‖ ^ 2
        = ∑ t ∈ Finset.range T, ∑ x : κ, ‖restrict (Q x) (psi t)‖ ^ 2 := Finset.sum_comm
      _ ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          have := sum_restrict_sq_le Q hQ (psi t)
          rw [hpsinorm t] at this; simpa using this
      _ = T := by simp
  -- Markov: few marked elements receive a lot of query weight
  set Bad : Finset κ := Finset.univ.filter (fun x : κ => 2 * T / N < q x) with hBaddef
  have hBad : (Bad.card : ℝ) < N / 2 := by
    rcases Finset.eq_empty_or_nonempty Bad with hB | hB
    · rw [hB]; simpa using by linarith [hNpos]
    · have hlt : (Bad.card : ℝ) * (2 * T / N) < ∑ x ∈ Bad, q x := by
        calc (Bad.card : ℝ) * (2 * T / N) = ∑ _x ∈ Bad, (2 * T / N) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ < ∑ x ∈ Bad, q x := by
              refine Finset.sum_lt_sum_of_nonempty hB (fun x hx => ?_)
              rw [hBaddef] at hx; simpa using (Finset.mem_filter.mp hx).2
      have hle : ∑ x ∈ Bad, q x ≤ T :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => hqnonneg x)) hqsum
      have hT : (Bad.card : ℝ) * (2 * T / N) < T := lt_of_lt_of_le hlt hle
      rcases Nat.eq_zero_or_pos T with hT0 | hT0
      · exfalso; rw [hT0] at hT; simp at hT
      · have hTpos : (0 : ℝ) < T := by exact_mod_cast hT0
        rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)] at *
        nlinarith [hT, hNpos, hTpos]
  -- most marked elements receive little query weight
  set Good : Finset κ := Finset.univ.filter (fun x : κ => ¬ (2 * T / N < q x)) with hGooddef
  have hcard : Bad.card + Good.card = N := by
    rw [hBaddef, hGooddef, ← hN, ← Finset.card_univ]
    exact Finset.filter_card_add_filter_neg_card_eq_card (p := fun x : κ => 2 * T / N < q x)
  have hGoodcard : 1 < Good.card := by
    by_contra hcon
    push_neg at hcon
    have h1 : (Good.card : ℝ) ≤ 1 := by exact_mod_cast hcon
    have h2 : (Bad.card : ℝ) + (Good.card : ℝ) = N := by exact_mod_cast hcard
    have h3 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hGoodcard
  have hgood : ∀ z ∈ Good, q z ≤ 2 * T / N := by
    intro z hz
    rw [hGooddef] at hz
    exact not_lt.mp (Finset.mem_filter.mp hz).2
  -- the hybrid argument bounds the distance to the oracle-free run
  have hdist : ∀ z ∈ Good, ‖run U (Q z) psi0 T - psi T‖ ^ 2 ≤ 8 * (T : ℝ) ^ 2 / N := by
    intro z hz
    have hh : ‖run U (Q z) psi0 T - psi T‖
        ≤ 2 * ∑ t ∈ Finset.range T, ‖restrict (Q z) (psi t)‖ := hybrid U (Q z) psi0 T
    have hcs : (∑ t ∈ Finset.range T, ‖restrict (Q z) (psi t)‖) ^ 2 ≤ (T : ℝ) * q z := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range T)
        (f := fun t => ‖restrict (Q z) (psi t)‖)
      simpa [hqdef] using this
    have hnn : 0 ≤ ∑ t ∈ Finset.range T, ‖restrict (Q z) (psi t)‖ := by positivity
    have hqz : q z ≤ 2 * T / N := hgood z hz
    have hTnn : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h5 : (T : ℝ) * q z ≤ (T : ℝ) * (2 * T / N) := by
      exact mul_le_mul_of_nonneg_left hqz hTnn
    have h6 : (T : ℝ) * (2 * T / N) = 2 * (T : ℝ) ^ 2 / N := by ring
    nlinarith [norm_nonneg (run U (Q z) psi0 T - psi T), hcs, hh, hnn]
  -- but success forces the two runs to be far apart
  have hfar : (0.239 : ℝ) ≤ ‖run U (Q x) psi0 T - run U (Q y) psi0 T‖ := by
    refine le_trans dist_const_lower ?_
    refine dist_of_success (Ans x) (Ans y) (hAns x y hxy) _ _ ?_ (hsucc x) (hsucc y)
    rw [run_norm, hpsi0]
  have htri : ‖run U (Q x) psi0 T - run U (Q y) psi0 T‖
      ≤ ‖run U (Q x) psi0 T - psi T‖ + ‖run U (Q y) psi0 T - psi T‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub (run U (Q x) psi0 T) (psi T) (run U (Q y) psi0 T)
    calc ‖run U (Q x) psi0 T - run U (Q y) psi0 T‖
        ≤ ‖run U (Q x) psi0 T - psi T‖ + ‖psi T - run U (Q y) psi0 T‖ := this
      _ = ‖run U (Q x) psi0 T - psi T‖ + ‖run U (Q y) psi0 T - psi T‖ := by
          rw [norm_sub_rev (psi T)]
  have hx' := hdist x hx
  have hy' := hdist y hy
  -- combine
  have hTsq : (N : ℝ) / 625 ≤ (T : ℝ) ^ 2 := by
    have hnx : 0 ≤ ‖run U (Q x) psi0 T - psi T‖ := norm_nonneg _
    have hny : 0 ≤ ‖run U (Q y) psi0 T - psi T‖ := norm_nonneg _
    have hsum2 : (0.239 : ℝ) ≤ ‖run U (Q x) psi0 T - psi T‖ + ‖run U (Q y) psi0 T - psi T‖ :=
      le_trans hfar htri
    have hkey : (0.239 : ℝ) ^ 2 ≤ 32 * (T : ℝ) ^ 2 / N := by nlinarith
    rw [le_div_iff₀ hNpos] at *
    nlinarith [hkey, hNpos]
  have hfinal : Real.sqrt ((N : ℝ) / 625) ≤ Real.sqrt ((T : ℝ) ^ 2) := Real.sqrt_le_sqrt hTsq
  rw [Real.sqrt_sq (Nat.cast_nonneg T)] at hfinal
  rw [show Real.sqrt (N : ℝ) / 25 = Real.sqrt ((N : ℝ) / 625) by
    rw [Real.sqrt_div_self']
  ] at *
  exact hfinal

end

end QI

