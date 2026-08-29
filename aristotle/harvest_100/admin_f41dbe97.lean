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
def restrict (S : Finset ι) (v : St ι) : St ι :=
  WithLp.toLp 2 (fun i => if i ∈ S then v i else 0)

@[simp] lemma restrict_apply (S : Finset ι) (v : St ι) (i : ι) :
    (restrict S v) i = if i ∈ S then v i else 0 := rfl

/-- The phase oracle flipping the sign of the coordinates in `S`. -/
def oracle (S : Finset ι) (v : St ι) : St ι :=
  WithLp.toLp 2 (fun i => if i ∈ S then -v i else v i)

@[simp] lemma oracle_apply (S : Finset ι) (v : St ι) (i : ι) :
    (oracle S v) i = if i ∈ S then -v i else v i := rfl

omit [DecidableEq ι] in
lemma norm_sq_eq (v : St ι) : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

lemma norm_restrict_sq (S : Finset ι) (v : St ι) : ‖restrict S v‖ ^ 2 = ∑ i ∈ S, ‖v i‖ ^ 2 := by
  rw [norm_sq_eq]
  calc ∑ i, ‖(restrict S v) i‖ ^ 2 = ∑ i ∈ S, ‖(restrict S v) i‖ ^ 2 :=
        (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])).symm
    _ = ∑ i ∈ S, ‖v i‖ ^ 2 := Finset.sum_congr rfl fun i hi => by simp [hi]

lemma restrict_sub (S : Finset ι) (v w : St ι) :
    restrict S (v - w) = restrict S v - restrict S w := by
  ext i; by_cases hi : i ∈ S <;> simp [restrict, hi]

lemma norm_restrict_le (S : Finset ι) (v : St ι) : ‖restrict S v‖ ≤ ‖v‖ := by
  have h1 : ‖restrict S v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_restrict_sq, norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by intros; positivity)
  nlinarith [norm_nonneg (restrict S v), norm_nonneg v]

lemma oracle_norm (S : Finset ι) (v : St ι) : ‖oracle S v‖ = ‖v‖ := by
  have h : ‖oracle S v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    exact Finset.sum_congr rfl (fun i _ => by by_cases hi : i ∈ S <;> simp [hi])
  nlinarith [norm_nonneg (oracle S v), norm_nonneg v]

lemma oracle_sub (S : Finset ι) (v w : St ι) : oracle S v - oracle S w = oracle S (v - w) := by
  ext i; by_cases hi : i ∈ S <;> simp [oracle, hi] <;> ring

/-- The oracle disturbs a state exactly in proportion to the amplitude it carries on
the queried coordinates. -/
lemma oracle_sub_self (S : Finset ι) (v : St ι) : ‖oracle S v - v‖ = 2 * ‖restrict S v‖ := by
  have h : oracle S v - v = (-2 : ℂ) • restrict S v := by
    ext i; by_cases hi : i ∈ S <;> simp [oracle, restrict, hi] <;> ring
  rw [h, norm_smul]
  norm_num

lemma oracle_empty (v : St ι) : oracle (∅ : Finset ι) v = v := by ext i; simp [oracle]

/-- The state of the algorithm after `t` queries to the oracle `oracle S`. -/
def run (U : ℕ → (St ι ≃ₗᵢ[ℂ] St ι)) (S : Finset ι) (psi0 : St ι) : ℕ → St ι
  | 0 => psi0
  | (t + 1) => U t (oracle S (run U S psi0 t))

lemma run_norm (U : ℕ → (St ι ≃ₗᵢ[ℂ] St ι)) (S : Finset ι) (psi0 : St ι) (t : ℕ) :
    ‖run U S psi0 t‖ = ‖psi0‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run, LinearIsometryEquiv.norm_map, oracle_norm, ih]

/-- **Hybrid argument.** The run with the oracle `oracle S` and the oracle-free run
differ by at most twice the total amplitude the oracle-free run places on `S`. -/
lemma hybrid (U : ℕ → (St ι ≃ₗᵢ[ℂ] St ι)) (S : Finset ι) (psi0 : St ι) (T : ℕ) :
    ‖run U S psi0 T - run U ∅ psi0 T‖
      ≤ 2 * ∑ t ∈ Finset.range T, ‖restrict S (run U ∅ psi0 t)‖ := by
  induction T with
  | zero => simp [run]
  | succ T ih =>
      have key : run U S psi0 (T + 1) - run U ∅ psi0 (T + 1)
          = U T (oracle S (run U S psi0 T)) - U T (oracle ∅ (run U ∅ psi0 T)) := rfl
      rw [key, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, oracle_empty]
      have h1 : ‖oracle S (run U S psi0 T) - run U ∅ psi0 T‖
          ≤ ‖oracle S (run U S psi0 T) - oracle S (run U ∅ psi0 T)‖
            + ‖oracle S (run U ∅ psi0 T) - run U ∅ psi0 T‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      rw [oracle_sub, oracle_norm, oracle_sub_self] at h1
      rw [Finset.sum_range_succ]
      linarith

/-- Total weight carried by a pairwise disjoint family of coordinate sets. -/
lemma sum_restrict_sq_le {κ : Type*} [Fintype κ] (Q : κ → Finset ι)
    (hQ : ∀ x y, x ≠ y → Disjoint (Q x) (Q y)) (v : St ι) :
    ∑ x, ‖restrict (Q x) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hdisj : ((Finset.univ : Finset κ) : Set κ).PairwiseDisjoint Q := by
    intro x _ y _ hxy; exact hQ x y hxy
  calc ∑ x, ‖restrict (Q x) v‖ ^ 2 = ∑ x, ∑ i ∈ Q x, ‖v i‖ ^ 2 :=
        Finset.sum_congr rfl fun x _ => norm_restrict_sq _ _
    _ = ∑ i ∈ Finset.univ.biUnion Q, ‖v i‖ ^ 2 := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ i, ‖v i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ = ‖v‖ ^ 2 := (norm_sq_eq v).symm

lemma two_restrict_sq_le (A B : Finset ι) (hAB : Disjoint A B) (v : St ι) :
    ‖restrict A v‖ ^ 2 + ‖restrict B v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_restrict_sq, norm_restrict_sq, norm_sq_eq, ← Finset.sum_union hAB]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

/-- Two unit states that are measured to give different outcomes with probability at
least `2/3` are at distance at least `√(2/3) - √(1/3)`. -/
lemma dist_of_success (A B : Finset ι) (hAB : Disjoint A B) (f g : St ι)
    (hg : ‖g‖ = 1) (hf : (2 : ℝ) / 3 ≤ ‖restrict A f‖ ^ 2)
    (hgB : (2 : ℝ) / 3 ≤ ‖restrict B g‖ ^ 2) :
    Real.sqrt (2 / 3) - Real.sqrt (1 / 3) ≤ ‖f - g‖ := by
  have hgA : ‖restrict A g‖ ^ 2 ≤ 1 / 3 := by
    have := two_restrict_sq_le A B hAB g
    rw [hg] at this; nlinarith
  have h1 : Real.sqrt (2 / 3) ≤ ‖restrict A f‖ := by
    rw [show ‖restrict A f‖ = Real.sqrt (‖restrict A f‖ ^ 2) by
      rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_le_sqrt hf
  have h2 : ‖restrict A g‖ ≤ Real.sqrt (1 / 3) := by
    rw [show ‖restrict A g‖ = Real.sqrt (‖restrict A g‖ ^ 2) by
      rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_le_sqrt hgA
  have h3 : ‖restrict A f‖ - ‖restrict A g‖ ≤ ‖restrict A f - restrict A g‖ :=
    norm_sub_norm_le _ _
  have h4 : ‖restrict A f - restrict A g‖ ≤ ‖f - g‖ := by
    rw [← restrict_sub]; exact norm_restrict_le _ _
  linarith

/-- Numerical bound on the distinguishability constant. -/
lemma dist_const_lower : (0.239 : ℝ) ≤ Real.sqrt (2 / 3) - Real.sqrt (1 / 3) := by
  have h1 : (0.8164 : ℝ) ≤ Real.sqrt (2 / 3) := by
    rw [show (0.8164 : ℝ) = Real.sqrt (0.8164 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : Real.sqrt (1 / 3) ≤ 0.5774 := by
    rw [show (0.5774 : ℝ) = Real.sqrt (0.5774 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **BBBV bound / optimality of Grover's algorithm.**

Let `κ` be a search space of size `N ≥ 2`.  Consider a `T`-query quantum algorithm:
it starts in a unit state `psi0`, alternates arbitrary unitaries `U t` with calls to
the phase oracle for the unknown marked element `x` (which flips the phase of the
basis states in `Q x`, these sets being pairwise disjoint), and finally announces its
answer by a measurement in the computational basis, outputting `x` when the outcome
lies in `Ans x` (again pairwise disjoint sets).  If the algorithm is correct with
probability at least `2/3` for every marked element, then `T ≥ √N / 25`.

Since Grover's algorithm achieves `O(√N)` queries, this shows it is optimal up to a
constant factor. -/
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

