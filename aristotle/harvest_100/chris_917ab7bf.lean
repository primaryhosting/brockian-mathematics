/-
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The BBBV lower bound for unstructured search

This file formalises the *hybrid argument* of Bennett, Bernstein, Brassard and Vazirani,
which shows that any quantum algorithm that distinguishes the empty database from each of the
`N` single-marked-item databases must make `Ω(√N)` oracle queries.  Consequently Grover's
algorithm, which uses `O(√N)` queries, is optimal.

### The model

* The algorithm's Hilbert space is `EuclideanSpace ℂ ι` for a finite index type `ι`
  (index register together with an arbitrary workspace).
* `idx : ι → Fin N` records, for each computational basis state, which of the `N` database
  entries is being queried.
* The oracle for a marked item `x : Fin N` is the phase oracle `phaseOracle idx x`, which
  negates exactly the amplitudes of the basis states querying `x`.  The *empty* database
  corresponds to the identity oracle.
* The algorithm is an arbitrary sequence `U : ℕ → E ≃ₗᵢ[ℂ] E` of unitaries interleaved with
  the oracle calls, started in an arbitrary unit vector `init`.
* `psi x` is the run against the oracle marking `x`, `phi` is the run against the empty
  database.

The conclusion is `c * √N ≤ 2 * T` whenever the two final states are at distance at least `c`
for *every* `x`, i.e. `T ≥ (c/2)·√N` queries are needed.
-/

namespace QI

open Finset

section

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- The phase oracle marking the database entry `x`: it negates the amplitude of every
computational basis state whose query register holds `x`. -/
noncomputable def phaseOracle (idx : ι → Fin N) (x : Fin N) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => if idx i = x then -(v.ofLp i) else v.ofLp i)

omit [Fintype ι] in
@[simp] lemma phaseOracle_ofLp (idx : ι → Fin N) (x : Fin N) (v : EuclideanSpace ℂ ι) (i : ι) :
    (phaseOracle idx x v).ofLp i = if idx i = x then -(v.ofLp i) else v.ofLp i := by
  simp [phaseOracle]

/-- The phase oracle is norm preserving (it is a diagonal unitary). -/
lemma norm_phaseOracle (idx : ι → Fin N) (x : Fin N) (v : EuclideanSpace ℂ ι) :
    ‖phaseOracle idx x v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [phaseOracle_ofLp]
  split <;> simp

/-- The phase oracle is additive on differences (it is linear). -/
lemma phaseOracle_sub (idx : ι → Fin N) (x : Fin N) (v w : EuclideanSpace ℂ ι) :
    phaseOracle idx x v - phaseOracle idx x w = phaseOracle idx x (v - w) := by
  ext i
  simp only [PiLp.sub_apply, phaseOracle_ofLp]
  split <;> ring

/-- The *query mass* of `x` in the state `v`: the total probability that the query register
holds the value `x`. -/
noncomputable def queryMass (idx : ι → Fin N) (x : Fin N) (v : EuclideanSpace ℂ ι) : ℝ :=
  ∑ i ∈ univ.filter (fun i => idx i = x), ‖v.ofLp i‖ ^ 2

lemma queryMass_nonneg (idx : ι → Fin N) (x : Fin N) (v : EuclideanSpace ℂ ι) :
    0 ≤ queryMass idx x v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The query masses of a state sum to its squared norm. -/
lemma sum_queryMass (idx : ι → Fin N) (v : EuclideanSpace ℂ ι) :
    ∑ x, queryMass idx x v = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_fiberwise _ _ _

/-- The key perturbation estimate: applying the oracle for `x` moves a state by exactly
twice the square root of its query mass at `x`. -/
lemma norm_phaseOracle_sub_self (idx : ι → Fin N) (x : Fin N) (v : EuclideanSpace ℂ ι) :
    ‖phaseOracle idx x v - v‖ = 2 * Real.sqrt (queryMass idx x v) := by
  have h : ‖phaseOracle idx x v - v‖ ^ 2 = (2 * Real.sqrt (queryMass idx x v)) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      mul_pow, Real.sq_sqrt (queryMass_nonneg idx x v)]
    rw [queryMass, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not univ
      (fun i => idx i = x) (fun i => ‖(phaseOracle idx x v - v).ofLp i‖ ^ 2)]
    have h1 : ∀ i ∈ univ.filter (fun i => idx i = x),
        ‖(phaseOracle idx x v - v).ofLp i‖ ^ 2 = 2 ^ 2 * ‖v.ofLp i‖ ^ 2 := by
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp only [PiLp.sub_apply, phaseOracle_ofLp, hi.2, if_pos]
      rw [show -v.ofLp i - v.ofLp i = (-2 : ℂ) * v.ofLp i by ring]
      rw [norm_mul]
      norm_num [mul_pow]
    have h2 : ∀ i ∈ univ.filter (fun i => ¬ (idx i = x)),
        ‖(phaseOracle idx x v - v).ofLp i‖ ^ 2 = 0 := by
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp only [PiLp.sub_apply, phaseOracle_ofLp, hi.2, if_neg, not_false_eq_true]
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
  have hnn : (0:ℝ) ≤ 2 * Real.sqrt (queryMass idx x v) := by positivity
  nlinarith [norm_nonneg (phaseOracle idx x v - v), h]

end

section

variable {ι : Type*} [Fintype ι] {N : ℕ}

local notation "E" => EuclideanSpace ℂ ι

/-- **Hybrid argument.** The run against the oracle marking `x` and the run against the empty
database differ, after `T` steps, by at most the total oracle perturbation along the
undisturbed run. -/
lemma hybrid_bound (idx : ι → Fin N) (x : Fin N) (U : ℕ → (E ≃ₗᵢ[ℂ] E))
    (psi phi : ℕ → E) (h0 : psi 0 = phi 0)
    (hpsi : ∀ t, psi (t + 1) = U t (phaseOracle idx x (psi t)))
    (hphi : ∀ t, phi (t + 1) = U t (phi t)) (T : ℕ) :
    ‖psi T - phi T‖ ≤ ∑ t ∈ range T, 2 * Real.sqrt (queryMass idx x (phi t)) := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
      rw [Finset.sum_range_succ]
      have step : ‖psi (T + 1) - phi (T + 1)‖
          = ‖phaseOracle idx x (psi T) - phi T‖ := by
        rw [hpsi, hphi, ← LinearIsometryEquiv.map_sub]
        exact LinearIsometryEquiv.norm_map _ _
      have tri : ‖phaseOracle idx x (psi T) - phi T‖
          ≤ ‖phaseOracle idx x (psi T) - phaseOracle idx x (phi T)‖
            + ‖phaseOracle idx x (phi T) - phi T‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub
          (phaseOracle idx x (psi T)) (phaseOracle idx x (phi T)) (phi T)
      have e1 : ‖phaseOracle idx x (psi T) - phaseOracle idx x (phi T)‖ = ‖psi T - phi T‖ := by
        rw [phaseOracle_sub, norm_phaseOracle]
      rw [step]
      rw [e1] at tri
      rw [norm_phaseOracle_sub_self] at tri
      linarith
end

/-- **Optimality of Grover's algorithm (BBBV lower bound).**

Let a quantum query algorithm act on the finite-dimensional Hilbert space `EuclideanSpace ℂ ι`,
where `idx i` is the database index queried by the computational basis state `i`.  The algorithm
starts in a unit vector `init` and alternates arbitrary unitaries `U t` with oracle calls.
`phi` is its run against the empty database (identity oracle), and `psi x` is its run against
the oracle marking the item `x`.

If after `T` queries the algorithm's state distinguishes the empty database from *every*
single-marked-item database by at least `c` in norm, then

  `c * √N ≤ 2 * T`,

i.e. `T ≥ (c/2)·√N`.  Since Grover's algorithm achieves a constant `c` with `O(√N)` queries,
it is optimal up to a constant factor. -/
theorem grover_optimal {ι : Type*} [Fintype ι] {N T : ℕ} (idx : ι → Fin N)
    (U : ℕ → (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι))
    (init : EuclideanSpace ℂ ι) (hinit : ‖init‖ = 1)
    (psi : Fin N → ℕ → EuclideanSpace ℂ ι) (phi : ℕ → EuclideanSpace ℂ ι)
    (hpsi0 : ∀ x, psi x 0 = init)
    (hpsi : ∀ x t, psi x (t + 1) = U t (phaseOracle idx x (psi x t)))
    (hphi0 : phi 0 = init)
    (hphi : ∀ t, phi (t + 1) = U t (phi t))
    (c : ℝ) (hdist : ∀ x, c ≤ ‖psi x T - phi T‖) :
    c * Real.sqrt N ≤ 2 * T := by
  classical
  -- the undisturbed run stays a unit vector
  have hnorm : ∀ t, ‖phi t‖ = 1 := by
    intro t
    induction t with
    | zero => rw [hphi0, hinit]
    | succ t ih => rw [hphi, LinearIsometryEquiv.norm_map, ih]
  -- total query mass of `x` along the undisturbed run
  set Q : Fin N → ℝ := fun x => ∑ t ∈ range T, queryMass idx x (phi t) with hQ
  have hQnonneg : ∀ x, 0 ≤ Q x := fun x =>
    Finset.sum_nonneg fun _ _ => queryMass_nonneg _ _ _
  have hQsum : ∑ x, Q x = T := by
    rw [hQ]
    rw [Finset.sum_comm]
    have : ∀ t ∈ range T, ∑ x, queryMass idx x (phi t) = 1 := by
      intro t _
      rw [sum_queryMass, hnorm t]; norm_num
    rw [Finset.sum_congr rfl this]
    simp
  -- per-`x` bound coming from the hybrid argument and Cauchy–Schwarz
  have hbound : ∀ x, c ≤ 2 * Real.sqrt T * Real.sqrt (Q x) := by
    intro x
    have h1 := hybrid_bound idx x U (psi x) phi (by rw [hpsi0, hphi0]) (hpsi x) hphi T
    have h2 : ∑ t ∈ range T, 2 * Real.sqrt (queryMass idx x (phi t))
        ≤ 2 * (Real.sqrt (Q x) * Real.sqrt T) := by
      rw [← Finset.mul_sum]
      have := Real.sum_sqrt_mul_sqrt_le (f := fun t => queryMass idx x (phi t))
        (g := fun _ : ℕ => (1:ℝ)) (range T)
        (fun t => queryMass_nonneg _ _ _) (fun _ => zero_le_one)
      simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one] at this
      have : ∑ t ∈ range T, Real.sqrt (queryMass idx x (phi t))
          ≤ Real.sqrt (Q x) * Real.sqrt T := by
        simpa [hQ] using this
      linarith
    have := le_trans (hdist x) (le_trans h1 h2)
    linarith [this]
  -- sum over `x` and apply Cauchy–Schwarz again
  have hsum : (N : ℝ) * c ≤ 2 * Real.sqrt T * ∑ x, Real.sqrt (Q x) := by
    have : ∑ _x : Fin N, c ≤ ∑ x, 2 * Real.sqrt T * Real.sqrt (Q x) :=
      Finset.sum_le_sum fun x _ => hbound x
    simpa [Finset.mul_sum, mul_comm] using this
  have hcs : ∑ x, Real.sqrt (Q x) ≤ Real.sqrt N * Real.sqrt T := by
    have := Real.sum_sqrt_mul_sqrt_le (f := Q) (g := fun _ : Fin N => (1:ℝ)) univ
      hQnonneg (fun _ => zero_le_one)
    simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    rw [hQsum] at this
    calc ∑ x, Real.sqrt (Q x) ≤ Real.sqrt T * Real.sqrt N := this
      _ = Real.sqrt N * Real.sqrt T := mul_comm _ _
  -- combine
  have hsT : Real.sqrt T * Real.sqrt T = (T : ℝ) := Real.mul_self_sqrt (by positivity)
  have key : (N : ℝ) * c ≤ 2 * Real.sqrt N * T := by
    have h3 : 2 * Real.sqrt T * ∑ x, Real.sqrt (Q x)
        ≤ 2 * Real.sqrt T * (Real.sqrt N * Real.sqrt T) := by
      have h4 : (0:ℝ) ≤ 2 * Real.sqrt T := by positivity
      exact mul_le_mul_of_nonneg_left hcs h4
    have e : 2 * Real.sqrt T * (Real.sqrt N * Real.sqrt T) = 2 * Real.sqrt N * (T : ℝ) := by
      linear_combination 2 * Real.sqrt N * hsT
    linarith [hsum, h3, e]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero]
    positivity
  · have hsN : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    have hNN : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (by positivity)
    refine le_of_mul_le_mul_left ?_ hsN
    calc Real.sqrt N * (c * Real.sqrt N) = (N : ℝ) * c := by linear_combination c * hNN
      _ ≤ 2 * Real.sqrt N * T := key
      _ = Real.sqrt N * (2 * T) := by ring

/-- Specialisation of the BBBV bound: an algorithm whose final states are perfectly
distinguishable (distance at least `1`) from the empty-database run, for every marked item,
must make at least `√N / 2` queries.  This is the `Ω(√N)` lower bound matched by Grover's
algorithm. -/
theorem grover_optimal_sqrt {ι : Type*} [Fintype ι] {N T : ℕ} (idx : ι → Fin N)
    (U : ℕ → (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι))
    (init : EuclideanSpace ℂ ι) (hinit : ‖init‖ = 1)
    (psi : Fin N → ℕ → EuclideanSpace ℂ ι) (phi : ℕ → EuclideanSpace ℂ ι)
    (hpsi0 : ∀ x, psi x 0 = init)
    (hpsi : ∀ x t, psi x (t + 1) = U t (phaseOracle idx x (psi x t)))
    (hphi0 : phi 0 = init)
    (hphi : ∀ t, phi (t + 1) = U t (phi t))
    (hdist : ∀ x, (1 : ℝ) ≤ ‖psi x T - phi T‖) :
    Real.sqrt N / 2 ≤ T := by
  have := grover_optimal idx U init hinit psi phi hpsi0 hpsi hphi0 hphi 1 hdist
  linarith [this]

/-!
### A self-contained instantiation

The hypotheses of `grover_optimal` are not vacuous: for *any* choice of unitaries, oracle and
initial state the two runs exist, being given by the obvious recursion.  The corollary
`grover_optimal_run` states the bound directly in terms of that recursion.
-/

/-- The state of a quantum query algorithm after `t` steps: starting from `init`, each step
applies the oracle `O` and then the unitary `U t`. -/
noncomputable def oracleRun {ι : Type*} [Fintype ι]
    (U : ℕ → (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι))
    (O : EuclideanSpace ℂ ι → EuclideanSpace ℂ ι) (init : EuclideanSpace ℂ ι) :
    ℕ → EuclideanSpace ℂ ι
  | 0 => init
  | t + 1 => U t (O (oracleRun U O init t))

@[simp] lemma oracleRun_zero {ι : Type*} [Fintype ι]
    (U : ℕ → (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι))
    (O : EuclideanSpace ℂ ι → EuclideanSpace ℂ ι) (init : EuclideanSpace ℂ ι) :
    oracleRun U O init 0 = init := rfl

@[simp] lemma oracleRun_succ {ι : Type*} [Fintype ι]
    (U : ℕ → (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι))
    (O : EuclideanSpace ℂ ι → EuclideanSpace ℂ ι) (init : EuclideanSpace ℂ ι) (t : ℕ) :
    oracleRun U O init (t + 1) = U t (O (oracleRun U O init t)) := rfl

/-- **BBBV lower bound, stated for the explicit runs.**  For an arbitrary quantum query
algorithm (unitaries `U`, unit initial state `init`), if after `T` queries the run against the
oracle marking `x` is at distance at least `c` from the run against the empty database, for
every `x : Fin N`, then `c * √N ≤ 2 * T`. -/
theorem grover_optimal_run {ι : Type*} [Fintype ι] {N T : ℕ} (idx : ι → Fin N)
    (U : ℕ → (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι))
    (init : EuclideanSpace ℂ ι) (hinit : ‖init‖ = 1) (c : ℝ)
    (hdist : ∀ x, c ≤ ‖oracleRun U (phaseOracle idx x) init T - oracleRun U id init T‖) :
    c * Real.sqrt N ≤ 2 * T :=
  grover_optimal idx U init hinit (fun x => oracleRun U (phaseOracle idx x) init)
    (oracleRun U id init) (fun _ => rfl) (fun _ _ => rfl) rfl (fun _ => rfl) c hdist

end QI

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

