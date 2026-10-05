/-
/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean requires `import` before any module docstring, so the required header block
-- above is enclosed in an ordinary block comment; its text is reproduced verbatim.)

import Mathlib

/-!
## The BBBV lower bound for unstructured search

We formalise the hybrid argument of Bennett–Bernstein–Brassard–Vazirani: any quantum
algorithm that finds a marked element among `N` possibilities with success probability
at least `2/3` must make `Ω(√N)` queries to the phase oracle.  In particular Grover's
algorithm, which uses `O(√N)` queries, is optimal up to a constant factor.

**The model.**  The state space is `QState N W = EuclideanSpace ℂ (Fin N × Fin W)`: the
first factor is the query register (holding an index `i < N`), the second factor is an
arbitrary workspace of dimension `W`.  The oracle for a marked element `x` is the phase
oracle `oracle x`, which flips the sign of every basis vector whose query register holds
`x`.  An algorithm is an arbitrary sequence `U 0, U 1, …` of norm preserving linear maps
(unitaries), applied alternately with oracle calls to a unit initial state, see `run`.
The algorithm succeeds if measuring the query register of the final state returns the
marked element, i.e. if `‖proj x (run U (oracle x) init T)‖ ^ 2 ≥ 2/3`.
-/

namespace QI

open scoped BigOperators

/-- The state space of the algorithm: an `N`-dimensional query register tensored with a
`W`-dimensional workspace. -/
abbrev QState (N W : ℕ) := EuclideanSpace ℂ (Fin N × Fin W)

/-- The orthogonal projection onto the subspace where the query register holds `x`. -/
def proj {N W : ℕ} (x : Fin N) (v : QState N W) : QState N W :=
  WithLp.toLp 2 (fun p => if p.1 = x then v p else 0)

/-- The phase oracle marking the element `x`: it flips the sign of the components whose
query register holds `x`. -/
def oracle {N W : ℕ} (x : Fin N) (v : QState N W) : QState N W :=
  WithLp.toLp 2 (fun p => if p.1 = x then -v p else v p)

/-- `run U O init t` is the state after `t` steps of the algorithm given by the unitaries
`U` acting on the initial state `init`, where each step consists of one call to the
oracle `O` followed by one unitary. -/
def run {N W : ℕ} (U : ℕ → QState N W →ₗ[ℂ] QState N W) (O : QState N W → QState N W)
    (init : QState N W) : ℕ → QState N W
  | 0 => init
  | t + 1 => U t (O (run U O init t))

@[simp] lemma proj_apply {N W : ℕ} (x : Fin N) (v : QState N W) (p : Fin N × Fin W) :
    (proj x v) p = if p.1 = x then v p else 0 := rfl

@[simp] lemma oracle_apply {N W : ℕ} (x : Fin N) (v : QState N W) (p : Fin N × Fin W) :
    (oracle x v) p = if p.1 = x then -v p else v p := rfl

@[simp] lemma run_zero {N W : ℕ} (U : ℕ → QState N W →ₗ[ℂ] QState N W)
    (O : QState N W → QState N W) (init : QState N W) : run U O init 0 = init := rfl

@[simp] lemma run_succ {N W : ℕ} (U : ℕ → QState N W →ₗ[ℂ] QState N W)
    (O : QState N W → QState N W) (init : QState N W) (t : ℕ) :
    run U O init (t + 1) = U t (O (run U O init t)) := rfl

/-- The squared norm of a state is the sum of the squared moduli of its amplitudes. -/
lemma normsq {N W : ℕ} (v : QState N W) : ‖v‖ ^ 2 = ∑ p, ‖v p‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

lemma proj_normsq {N W : ℕ} (x : Fin N) (v : QState N W) :
    ‖proj x v‖ ^ 2 = ∑ p, if p.1 = x then ‖v p‖ ^ 2 else 0 := by
  rw [normsq]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [proj_apply]
  split_ifs <;> simp

/-- The projections onto the `N` values of the query register resolve the identity. -/
lemma sum_proj_normsq {N W : ℕ} (v : QState N W) :
    ∑ x : Fin N, ‖proj x v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp only [proj_normsq]
  rw [Finset.sum_comm, normsq]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

lemma norm_proj_le {N W : ℕ} (x : Fin N) (v : QState N W) : ‖proj x v‖ ≤ ‖v‖ := by
  have h : ‖proj x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [proj_normsq, normsq]
    refine Finset.sum_le_sum fun p _ => ?_
    split_ifs
    · exact le_rfl
    · positivity
  nlinarith [norm_nonneg (proj x v), norm_nonneg v]

lemma proj_sub {N W : ℕ} (x : Fin N) (u v : QState N W) :
    proj x u - proj x v = proj x (u - v) := by
  ext p
  simp only [PiLp.sub_apply, proj_apply]
  split_ifs <;> simp

/-- The phase oracle is an isometry. -/
lemma oracle_isometry {N W : ℕ} (x : Fin N) (u v : QState N W) :
    ‖oracle x u - oracle x v‖ = ‖u - v‖ := by
  have key : ‖oracle x u - oracle x v‖ ^ 2 = ‖u - v‖ ^ 2 := by
    rw [normsq, normsq]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [PiLp.sub_apply, oracle_apply]
    split_ifs with h
    · rw [show -u.ofLp p - -v.ofLp p = -(u.ofLp p - v.ofLp p) by ring, norm_neg]
    · rfl
  nlinarith [norm_nonneg (oracle x u - oracle x v), norm_nonneg (u - v)]

/-- A query only disturbs the state through the branch on which it acts. -/
lemma oracle_sub_self {N W : ℕ} (x : Fin N) (v : QState N W) :
    ‖oracle x v - v‖ = 2 * ‖proj x v‖ := by
  have key : ‖oracle x v - v‖ ^ 2 = (2 * ‖proj x v‖) ^ 2 := by
    rw [normsq, mul_pow, proj_normsq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [PiLp.sub_apply, oracle_apply]
    split_ifs with h
    · rw [show -v.ofLp p - v.ofLp p = -(2 * v.ofLp p) by ring, norm_neg, norm_mul]
      simp [mul_pow]
    · simp
  nlinarith [norm_nonneg (oracle x v - v), norm_nonneg (proj x v)]

/-- The oracle-free run stays a unit vector. -/
lemma norm_run_free {N W : ℕ} (U : ℕ → QState N W →ₗ[ℂ] QState N W)
    (hU : ∀ t v, ‖U t v‖ = ‖v‖) (init : QState N W) (t : ℕ) :
    ‖run U id init t‖ = ‖init‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, id, hU, ih]

/-- **The hybrid argument.**  The final state of the algorithm run with the oracle marking
`x` differs from the final state of the oracle-free run by at most twice the total
amplitude that the oracle-free run places on the branch `x`. -/
lemma hybrid {N W : ℕ} (U : ℕ → QState N W →ₗ[ℂ] QState N W)
    (hU : ∀ t v, ‖U t v‖ = ‖v‖) (init : QState N W) (x : Fin N) (T : ℕ) :
    ‖run U (oracle x) init T - run U id init T‖
      ≤ 2 * ∑ t ∈ Finset.range T, ‖proj x (run U id init t)‖ := by
  induction T with
  | zero => simp
  | succ T ih =>
      set ψ := run U (oracle x) init T
      set φ := run U id init T
      have step : run U (oracle x) init (T + 1) - run U id init (T + 1)
          = U T (oracle x ψ - φ) := by
        rw [run_succ, run_succ, map_sub]
        rfl
      rw [step, hU]
      have h1 : ‖oracle x ψ - φ‖ ≤ ‖oracle x ψ - oracle x φ‖ + ‖oracle x φ - φ‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub (oracle x ψ) (oracle x φ) φ
      rw [oracle_isometry, oracle_sub_self] at h1
      rw [Finset.sum_range_succ]
      linarith
end QI

namespace QI

/-- **Optimality of Grover search (BBBV lower bound).**

Any quantum algorithm for unstructured search over `N` elements, given by an arbitrary
initial unit state, arbitrary unitaries `U t` (norm preserving linear maps on the state
space, with an arbitrary workspace `Fin W`) and `T` calls to the phase oracle marking the
hidden element, which finds the hidden element with probability at least `2/3` for every
possible hidden element, must satisfy `√N ≤ 4 * T + 2`, i.e. `T ≥ (√N - 2)/4 = Ω(√N)`.

Since Grover's algorithm achieves `O(√N)` queries, this bound shows it is optimal up to
a constant factor. -/
theorem grover_optimal {N W T : ℕ}
    (U : ℕ → QState N W →ₗ[ℂ] QState N W) (hU : ∀ t v, ‖U t v‖ = ‖v‖)
    (init : QState N W) (hinit : ‖init‖ = 1)
    (hsucc : ∀ x : Fin N, (2 : ℝ) / 3 ≤ ‖proj x (run U (oracle x) init T)‖ ^ 2) :
    Real.sqrt N ≤ 4 * T + 2 := by
  set φ : ℕ → QState N W := fun t => run U id init t with hφ
  set a : Fin N → ℝ := fun x => ‖proj x (φ T)‖ with ha
  set b : Fin N → ℝ := fun x => ‖run U (oracle x) init T - φ T‖ with hb
  set S : Fin N → ℝ := fun x => ∑ t ∈ Finset.range T, ‖proj x (φ t)‖ with hS
  -- Every `φ t` is a unit vector.
  have hunit : ∀ t, ‖φ t‖ = 1 := fun t => by rw [hφ, norm_run_free U hU init t, hinit]
  -- Hybrid bound.
  have h1 : ∀ x, b x ≤ 2 * S x := fun x => hybrid U hU init x T
  -- Cauchy-Schwarz plus resolution of the identity.
  have h2 : ∑ x : Fin N, S x ^ 2 ≤ (T : ℝ) ^ 2 := by
    have cs : ∀ x : Fin N, S x ^ 2 ≤ (T : ℝ) * ∑ t ∈ Finset.range T, ‖proj x (φ t)‖ ^ 2 := by
      intro x
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range T)
        (f := fun t => ‖proj x (φ t)‖)
      simpa using this
    calc ∑ x : Fin N, S x ^ 2
        ≤ ∑ x : Fin N, (T : ℝ) * ∑ t ∈ Finset.range T, ‖proj x (φ t)‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => cs x
      _ = (T : ℝ) * ∑ t ∈ Finset.range T, ∑ x : Fin N, ‖proj x (φ t)‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ = (T : ℝ) ^ 2 := by
          simp only [sum_proj_normsq, hunit, one_pow]
          simp [sq]
  have h3 : ∑ x : Fin N, b x ^ 2 ≤ 4 * (T : ℝ) ^ 2 := by
    have : ∑ x : Fin N, b x ^ 2 ≤ ∑ x : Fin N, 4 * S x ^ 2 := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hbx : 0 ≤ b x := norm_nonneg _
      nlinarith [h1 x]
    calc ∑ x : Fin N, b x ^ 2 ≤ ∑ x : Fin N, 4 * S x ^ 2 := this
      _ = 4 * ∑ x : Fin N, S x ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * (T : ℝ) ^ 2 := by linarith
  have h4 : ∑ x : Fin N, a x ^ 2 = 1 := by
    show ∑ x : Fin N, ‖proj x (φ T)‖ ^ 2 = 1
    rw [sum_proj_normsq, hunit T, one_pow]
  -- Pointwise success bound.
  have h5 : ∀ x : Fin N, (2 : ℝ) / 3 ≤ 2 * a x ^ 2 + 2 * b x ^ 2 := by
    intro x
    set ψ := run U (oracle x) init T with hψ
    have hle : ‖proj x ψ‖ ≤ a x + b x := by
      have : ‖proj x ψ‖ ≤ ‖proj x (φ T)‖ + ‖proj x ψ - proj x (φ T)‖ := by
        simpa using norm_le_norm_add_norm_sub' (proj x ψ) (proj x (φ T))
      have h' : ‖proj x ψ - proj x (φ T)‖ ≤ b x := by
        rw [proj_sub]
        exact norm_proj_le x _
      linarith
    have h0 : 0 ≤ ‖proj x ψ‖ := norm_nonneg _
    have hax : 0 ≤ a x := norm_nonneg _
    have hbx : 0 ≤ b x := norm_nonneg _
    have hsq : ‖proj x ψ‖ ^ 2 ≤ (a x + b x) ^ 2 := by nlinarith
    nlinarith [hsucc x, sq_nonneg (a x - b x)]
  -- Averaging over the `N` possible marked elements.
  have h6 : (2 : ℝ) / 3 * N ≤ 2 * 1 + 2 * (4 * (T : ℝ) ^ 2) := by
    have : (2 : ℝ) / 3 * N ≤ ∑ x : Fin N, (2 * a x ^ 2 + 2 * b x ^ 2) := by
      calc (2 : ℝ) / 3 * N = ∑ _x : Fin N, (2 : ℝ) / 3 := by
            simp [Finset.sum_const, mul_comm]
        _ ≤ ∑ x : Fin N, (2 * a x ^ 2 + 2 * b x ^ 2) := Finset.sum_le_sum fun x _ => h5 x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h4] at this
    linarith
  have hN : (N : ℝ) ≤ (4 * (T : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) T]
  calc Real.sqrt N ≤ Real.sqrt ((4 * (T : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt hN
    _ = 4 * T + 2 := Real.sqrt_sq (by positivity)

/-- The hypotheses of `grover_optimal` are satisfiable, so the theorem is not vacuous:
for `N = W = 1` the trivial zero-query algorithm finds the marked element with
probability `1`. -/
theorem grover_hypotheses_satisfiable :
    ∃ (U : ℕ → QState 1 1 →ₗ[ℂ] QState 1 1) (init : QState 1 1),
      (∀ t v, ‖U t v‖ = ‖v‖) ∧ ‖init‖ = 1 ∧
        ∀ x : Fin 1, (2 : ℝ) / 3 ≤ ‖proj x (run U (oracle x) init 0)‖ ^ 2 := by
  refine ⟨fun _ => LinearMap.id, EuclideanSpace.single (0, 0) 1, fun _ _ => rfl, by simp, ?_⟩
  intro x
  have h : ‖proj x (run (fun _ => LinearMap.id) (oracle x)
      (EuclideanSpace.single ((0 : Fin 1), (0 : Fin 1)) 1) 0)‖ ^ 2 = 1 := by
    rw [proj_normsq]
    simp [EuclideanSpace.single_apply, Prod.ext_iff, Fin.eq_zero]
  rw [h]
  norm_num

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

