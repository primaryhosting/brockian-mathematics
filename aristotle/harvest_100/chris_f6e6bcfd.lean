import Mathlib
/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command of a module, so the header
-- module docstring above is placed immediately after the single `import Mathlib` line.)

/-!
## The BBBV lower bound for unstructured search

We formalise the Bennett–Bernstein–Brassard–Vazirani hybrid argument: any quantum
algorithm that finds a marked item among `N` possibilities with success probability
at least `2/3` must make `Ω(√N)` queries to the oracle.

**The model.**  The workspace is the finite dimensional Hilbert space
`QState N W = EuclideanSpace ℂ (Fin N × Fin W)`: an index register holding one of the
`N` candidate items, tensored with an arbitrary `W`-dimensional workspace.
For a marked item `x : Fin N`, the (phase) oracle `oracle x` flips the sign of every
basis vector whose index register equals `x`; it is a norm preserving linear map.
An algorithm consists of a unit initial state `psi0` and an arbitrary sequence
`U : ℕ → QState N W →ₗᵢ[ℂ] QState N W` of linear isometries (in particular every
unitary is allowed).  With oracle `x` the state after `t` queries is
`runOracle U psi0 x t`, and `runFree U psi0 t` is the corresponding oracle-free run.
The algorithm answers by measuring the index register of its final state, so its
success probability on input `x` is `‖proj x (runOracle U psi0 x T)‖ ^ 2`.

**The result** (`QI.grover_optimal`): if `6 ≤ N` and the algorithm succeeds with
probability at least `2/3` on *every* marked item `x`, then `√N / 20 ≤ T`.
Since Grover's algorithm achieves `O(√N)` queries, this is optimal up to constants.
-/

namespace QI

open Finset

/-- The state space of the search algorithm: an `N`-dimensional index register
tensored with a `W`-dimensional workspace. -/
abbrev QState (N W : ℕ) := EuclideanSpace ℂ (Fin N × Fin W)

variable {N W : ℕ}

/-- Orthogonal projection onto the subspace where the index register holds `x`. -/
noncomputable def proj (x : Fin N) (v : QState N W) : QState N W :=
  WithLp.toLp 2 fun p => if p.1 = x then v.ofLp p else 0

/-- The phase oracle for the marked item `x`: it negates the amplitude of every basis
state whose index register holds `x`. -/
noncomputable def oracle (x : Fin N) (v : QState N W) : QState N W :=
  WithLp.toLp 2 fun p => if p.1 = x then -(v.ofLp p) else v.ofLp p

@[simp] lemma proj_apply (x : Fin N) (v : QState N W) (p : Fin N × Fin W) :
    (proj x v).ofLp p = if p.1 = x then v.ofLp p else 0 := rfl

@[simp] lemma oracle_apply (x : Fin N) (v : QState N W) (p : Fin N × Fin W) :
    (oracle x v).ofLp p = if p.1 = x then -(v.ofLp p) else v.ofLp p := rfl

/-- The state of the algorithm after `t` queries to the oracle for the marked item `x`. -/
noncomputable def runOracle (U : ℕ → (QState N W →ₗᵢ[ℂ] QState N W)) (psi0 : QState N W)
    (x : Fin N) : ℕ → QState N W
  | 0 => psi0
  | t + 1 => U t (oracle x (runOracle U psi0 x t))

/-- The state of the algorithm after `t` steps when the oracle answers no queries
(the "empty" oracle, i.e. no marked item). -/
noncomputable def runFree (U : ℕ → (QState N W →ₗᵢ[ℂ] QState N W)) (psi0 : QState N W) :
    ℕ → QState N W
  | 0 => psi0
  | t + 1 => U t (runFree U psi0 t)

/-! ### Elementary properties of the oracle and the projections -/

lemma norm_oracle (x : Fin N) (v : QState N W) : ‖oracle x v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [oracle_apply]
  split_ifs <;> simp

lemma oracle_sub (x : Fin N) (v w : QState N W) :
    oracle x (v - w) = oracle x v - oracle x w := by
  ext p
  by_cases h : p.1 = x <;> simp [h]
  ring

lemma proj_sub (x : Fin N) (v w : QState N W) :
    proj x (v - w) = proj x v - proj x w := by
  ext p
  by_cases h : p.1 = x <;> simp [h]

lemma oracle_sub_self (x : Fin N) (v : QState N W) :
    oracle x v - v = (-2 : ℂ) • proj x v := by
  ext p
  by_cases h : p.1 = x <;> simp [h]
  ring

lemma norm_oracle_sub_self (x : Fin N) (v : QState N W) :
    ‖oracle x v - v‖ = 2 * ‖proj x v‖ := by
  rw [oracle_sub_self, norm_smul]
  simp

lemma norm_proj_le (x : Fin N) (v : QState N W) : ‖proj x v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun p _ => ?_
  simp only [proj_apply]
  split_ifs <;> simp

/-- Pythagoras: the squared norms of the components of a state sum to its squared norm. -/
lemma sum_norm_proj_sq (v : QState N W) : ∑ x : Fin N, ‖proj x v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h : ∀ x : Fin N, ‖proj x v‖ ^ 2 = ∑ p : Fin N × Fin W, ‖(proj x v).ofLp p‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
    positivity
  simp only [h]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h3 : ∀ x : Fin N, ‖(if p.1 = x then v.ofLp p else 0 : ℂ)‖ ^ 2
      = if p.1 = x then ‖v.ofLp p‖ ^ 2 else 0 := by
    intro x; split_ifs <;> simp
  simp only [proj_apply, h3]
  simp

/-! ### The runs are unit vectors -/

lemma norm_runFree (U : ℕ → (QState N W →ₗᵢ[ℂ] QState N W)) (psi0 : QState N W) (t : ℕ) :
    ‖runFree U psi0 t‖ = ‖psi0‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runFree, LinearIsometry.norm_map, ih]

lemma norm_runOracle (U : ℕ → (QState N W →ₗᵢ[ℂ] QState N W)) (psi0 : QState N W)
    (x : Fin N) (t : ℕ) : ‖runOracle U psi0 x t‖ = ‖psi0‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runOracle, LinearIsometry.norm_map, norm_oracle, ih]

/-! ### The hybrid argument -/

/-- **Hybrid argument.** The distance between the run with oracle `x` and the oracle-free
run is at most twice the total amplitude that the oracle-free run places on index `x`. -/
lemma hybrid (U : ℕ → (QState N W →ₗᵢ[ℂ] QState N W)) (psi0 : QState N W) (x : Fin N)
    (T : ℕ) :
    ‖runOracle U psi0 x T - runFree U psi0 T‖
      ≤ 2 * ∑ t ∈ Finset.range T, ‖proj x (runFree U psi0 t)‖ := by
  induction T with
  | zero => simp [runOracle, runFree]
  | succ T ih =>
      have key : ‖runOracle U psi0 x (T + 1) - runFree U psi0 (T + 1)‖
          ≤ ‖runOracle U psi0 x T - runFree U psi0 T‖ + 2 * ‖proj x (runFree U psi0 T)‖ := by
        have h1 : runOracle U psi0 x (T + 1) - runFree U psi0 (T + 1)
            = U T (oracle x (runOracle U psi0 x T) - runFree U psi0 T) := by
          rw [runOracle, runFree, map_sub]
        rw [h1, LinearIsometry.norm_map]
        have h2 : oracle x (runOracle U psi0 x T) - runFree U psi0 T
            = oracle x (runOracle U psi0 x T - runFree U psi0 T)
              + (oracle x (runFree U psi0 T) - runFree U psi0 T) := by
          rw [oracle_sub]; abel
        calc ‖oracle x (runOracle U psi0 x T) - runFree U psi0 T‖
            ≤ ‖oracle x (runOracle U psi0 x T - runFree U psi0 T)‖
              + ‖oracle x (runFree U psi0 T) - runFree U psi0 T‖ := by
              rw [h2]; exact norm_add_le _ _
          _ = ‖runOracle U psi0 x T - runFree U psi0 T‖ + 2 * ‖proj x (runFree U psi0 T)‖ := by
              rw [norm_oracle, norm_oracle_sub_self]
      rw [Finset.sum_range_succ, mul_add]
      linarith [ih]

/-! ### The main theorem -/

/-- **BBBV / optimality of Grover search.**
Any quantum algorithm (unit initial state `psi0`, arbitrary linear isometries `U t`
interleaved with `T` phase-oracle queries) that finds the marked item with success
probability at least `2/3` for *every* marked item `x : Fin N` must satisfy
`T ≥ √N / 20`.  Hence unstructured search requires `Ω(√N)` queries, and Grover's
algorithm, which uses `O(√N)` queries, is optimal up to a constant factor. -/
theorem grover_optimal {N W T : ℕ} (hN : 6 ≤ N)
    (U : ℕ → (QState N W →ₗᵢ[ℂ] QState N W)) (psi0 : QState N W) (hpsi0 : ‖psi0‖ = 1)
    (hsucc : ∀ x : Fin N, (2 : ℝ) / 3 ≤ ‖proj x (runOracle U psi0 x T)‖ ^ 2) :
    Real.sqrt N / 20 ≤ (T : ℝ) := by
  classical
  have hfree_norm : ∀ t, ‖runFree U psi0 t‖ = 1 := fun t => by rw [norm_runFree, hpsi0]
  -- `m x` is the total weight the oracle-free run places on index `x`.
  set m : Fin N → ℝ := fun x => ∑ t ∈ Finset.range T, ‖proj x (runFree U psi0 t)‖ ^ 2 with hmdef
  have hm_nonneg : ∀ x, 0 ≤ m x := fun x => Finset.sum_nonneg fun t _ => by positivity
  have hmsum : ∑ x : Fin N, m x = (T : ℝ) := by
    have hstep : ∀ t ∈ Finset.range T,
        ∑ x : Fin N, ‖proj x (runFree U psi0 t)‖ ^ 2 = (1 : ℝ) := by
      intro t _
      rw [sum_norm_proj_sq, hfree_norm t]; norm_num
    simp only [hmdef]
    rw [Finset.sum_comm, Finset.sum_congr rfl hstep]
    simp
  -- Hybrid argument plus Cauchy–Schwarz.
  have hdist : ∀ x : Fin N, ‖runOracle U psi0 x T - runFree U psi0 T‖
      ≤ 2 * Real.sqrt T * Real.sqrt (m x) := by
    intro x
    refine le_trans (hybrid U psi0 x T) ?_
    have hcs : (∑ t ∈ Finset.range T, ‖proj x (runFree U psi0 t)‖) ^ 2 ≤ (T : ℝ) * m x := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range T) (fun _ => (1 : ℝ))
        (fun t => ‖proj x (runFree U psi0 t)‖)
      simpa [hmdef] using h
    have hnn : 0 ≤ ∑ t ∈ Finset.range T, ‖proj x (runFree U psi0 t)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hTm : (0 : ℝ) ≤ (T : ℝ) * m x := mul_nonneg (by positivity) (hm_nonneg x)
    have hle : (∑ t ∈ Finset.range T, ‖proj x (runFree U psi0 t)‖)
        ≤ Real.sqrt ((T : ℝ) * m x) := by
      nlinarith [Real.sq_sqrt hTm, Real.sqrt_nonneg ((T : ℝ) * m x)]
    rw [Real.sqrt_mul (by positivity)] at hle
    linarith
  -- The few indices on which the oracle-free run already has large weight.
  obtain ⟨B, hBmem⟩ : ∃ B : Finset (Fin N),
      ∀ x, x ∈ B ↔ (1 : ℝ) / 3 < ‖proj x (runFree U psi0 T)‖ ^ 2 :=
    ⟨Finset.univ.filter fun x => (1 : ℝ) / 3 < ‖proj x (runFree U psi0 T)‖ ^ 2, by
      intro x; simp⟩
  have hBcard : (B.card : ℝ) ≤ 3 := by
    have h1 : ∑ x ∈ B, ‖proj x (runFree U psi0 T)‖ ^ 2 ≤ 1 := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun i _ _ => sq_nonneg ‖proj i (runFree U psi0 T)‖)
      rw [sum_norm_proj_sq, hfree_norm T] at h
      simpa using h
    have h2 : (B.card : ℝ) * (1 / 3) ≤ ∑ x ∈ B, ‖proj x (runFree U psi0 T)‖ ^ 2 := by
      have h := Finset.card_nsmul_le_sum B (fun x => ‖proj x (runFree U psi0 T)‖ ^ 2) (1 / 3)
        (fun x hx => le_of_lt ((hBmem x).mp hx))
      simpa [nsmul_eq_mul] using h
    linarith
  -- On every other index the two runs are far apart.
  have hgood : ∀ x ∈ Finset.univ \ B,
      (1 : ℝ) / 5 ≤ ‖runOracle U psi0 x T - runFree U psi0 T‖ := by
    intro x hx
    have hxB : ¬ ((1 : ℝ) / 3 < ‖proj x (runFree U psi0 T)‖ ^ 2) := fun h =>
      (Finset.mem_sdiff.mp hx).2 ((hBmem x).mpr h)
    push_neg at hxB
    have h1 : ‖proj x (runOracle U psi0 x T) - proj x (runFree U psi0 T)‖
        ≤ ‖runOracle U psi0 x T - runFree U psi0 T‖ := by
      rw [← proj_sub]; exact norm_proj_le _ _
    have h2 : ‖proj x (runOracle U psi0 x T)‖ - ‖proj x (runFree U psi0 T)‖
        ≤ ‖proj x (runOracle U psi0 x T) - proj x (runFree U psi0 T)‖ := norm_sub_norm_le _ _
    have h3 := hsucc x
    nlinarith [norm_nonneg (proj x (runOracle U psi0 x T)),
      norm_nonneg (proj x (runFree U psi0 T)),
      sq_nonneg (‖proj x (runOracle U psi0 x T)‖ - ‖proj x (runFree U psi0 T)‖),
      sq_nonneg (‖proj x (runOracle U psi0 x T)‖ + ‖proj x (runFree U psi0 T)‖),
      sq_nonneg (‖proj x (runFree U psi0 T)‖ - 1)]
  -- Counting.
  have hcards : (Finset.univ \ B).card + B.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B), Finset.card_univ,
      Fintype.card_fin]
  have hcardR : (N : ℝ) - 3 ≤ ((Finset.univ \ B).card : ℝ) := by
    have hc : (((Finset.univ \ B).card : ℕ) : ℝ) + (B.card : ℝ) = (N : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcards
    linarith
  have hsum_good : ((Finset.univ \ B).card : ℝ) * (1 / 5)
      ≤ ∑ x ∈ Finset.univ \ B, ‖runOracle U psi0 x T - runFree U psi0 T‖ := by
    have h := Finset.card_nsmul_le_sum (Finset.univ \ B)
      (fun x => ‖runOracle U psi0 x T - runFree U psi0 T‖) (1 / 5) hgood
    simpa [nsmul_eq_mul] using h
  have hsum_all : ∑ x ∈ Finset.univ \ B, ‖runOracle U psi0 x T - runFree U psi0 T‖
      ≤ ∑ x : Fin N, ‖runOracle U psi0 x T - runFree U psi0 T‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => norm_nonneg _)
  have hsqrtsum : ∑ x : Fin N, Real.sqrt (m x) ≤ Real.sqrt ((N : ℝ) * T) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ))
      (fun x => Real.sqrt (m x))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Real.sq_sqrt (hm_nonneg _)] at h
    rw [hmsum] at h
    have hnn : 0 ≤ ∑ x : Fin N, Real.sqrt (m x) :=
      Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    have hNT : (0 : ℝ) ≤ (N : ℝ) * T := by positivity
    nlinarith [Real.sq_sqrt hNT, Real.sqrt_nonneg ((N : ℝ) * T)]
  have hsum_bound : ∑ x : Fin N, ‖runOracle U psi0 x T - runFree U psi0 T‖
      ≤ 2 * Real.sqrt T * ∑ x : Fin N, Real.sqrt (m x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hdist x
  -- Put everything together.
  have hkey : Real.sqrt T * Real.sqrt ((N : ℝ) * T) = Real.sqrt N * T := by
    rw [Real.sqrt_mul (by positivity)]
    have h : Real.sqrt T * Real.sqrt T = (T : ℝ) := Real.mul_self_sqrt (by positivity)
    linear_combination Real.sqrt N * h
  have hsT : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hfinal : ((N : ℝ) - 3) * (1 / 5) ≤ 2 * (Real.sqrt N * T) := by
    have hchain : ((Finset.univ \ B).card : ℝ) * (1 / 5)
        ≤ 2 * Real.sqrt T * Real.sqrt ((N : ℝ) * T) := by
      refine le_trans hsum_good (le_trans hsum_all (le_trans hsum_bound ?_))
      exact mul_le_mul_of_nonneg_left hsqrtsum (by linarith)
    rw [mul_assoc, hkey] at hchain
    nlinarith [hcardR, hchain]
  have hs : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (by positivity)
  have hNR : (6 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  nlinarith [hfinal, hs, hspos, hNR]

end QI

#print axioms QI.grover_optimal

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

