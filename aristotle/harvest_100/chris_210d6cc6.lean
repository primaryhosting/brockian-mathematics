import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

section Setup

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition function of the energy landscape `E k` at inverse temperature `beta`. -/
noncomputable def partitionFn (E : ℕ → X → ℝ) (beta : ℝ) (k : ℕ) : ℝ :=
  ∑ x : X, Real.exp (-beta * E k x)

lemma partitionFn_pos (E : ℕ → X → ℝ) (beta : ℝ) (k : ℕ) : 0 < partitionFn E beta k := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- Work performed on the system along the trajectory `x` during the protocol
`E 0, E 1, …, E N`: at step `k` the energy function is switched from `E k` to `E (k+1)`
while the system sits in state `x k`. -/
def work (E : ℕ → X → ℝ) (N : ℕ) (x : ℕ → X) : ℝ :=
  ∑ k ∈ Finset.range N, (E (k + 1) (x k) - E k (x k))

/-- Probability weight of the forward trajectory `x`: equilibrium initial condition at `E 0`
followed by the relaxation kernels `T 0, …, T (N-1)`. -/
noncomputable def forwardProb (E : ℕ → X → ℝ) (T : ℕ → X → X → ℝ) (beta : ℝ) (N : ℕ)
    (x : ℕ → X) : ℝ :=
  Real.exp (-beta * E 0 (x 0)) / partitionFn E beta 0 *
    ∏ k ∈ Finset.range N, T k (x k) (x (k + 1))

/-- Probability weight of a trajectory `y` under the time-reversed protocol: equilibrium initial
condition at `E N`, and the kernels applied in reverse order. -/
noncomputable def reverseProb (E : ℕ → X → ℝ) (T : ℕ → X → X → ℝ) (beta : ℝ) (N : ℕ)
    (y : ℕ → X) : ℝ :=
  Real.exp (-beta * E N (y 0)) / partitionFn E beta N *
    ∏ j ∈ Finset.range N, T (N - 1 - j) (y j) (y (j + 1))

/-- Time reversal of a trajectory of length `N`. -/
def reversePath (N : ℕ) (x : ℕ → X) : ℕ → X := fun j => x (N - j)

/-- Free-energy difference between the final and the initial equilibrium ensembles. -/
noncomputable def freeEnergyDiff (E : ℕ → X → ℝ) (beta : ℝ) (N : ℕ) : ℝ :=
  -(1 / beta) * Real.log (partitionFn E beta N / partitionFn E beta 0)

lemma exp_neg_beta_freeEnergyDiff (E : ℕ → X → ℝ) (beta : ℝ) (N : ℕ) (hbeta : beta ≠ 0) :
    Real.exp (-beta * freeEnergyDiff E beta N)
      = partitionFn E beta N / partitionFn E beta 0 := by
  unfold freeEnergyDiff
  have h : -beta * (-(1 / beta) * Real.log (partitionFn E beta N / partitionFn E beta 0))
      = Real.log (partitionFn E beta N / partitionFn E beta 0) := by
    field_simp
  rw [h, Real.exp_log]
  exact div_pos (partitionFn_pos E beta N) (partitionFn_pos E beta 0)

/-- Detailed balance: after the work step `k` the kernel `T k` is in detailed balance with
respect to the (new) energy function `E (k+1)`. -/
def DetailedBalance (E : ℕ → X → ℝ) (T : ℕ → X → X → ℝ) (beta : ℝ) : Prop :=
  ∀ k a b, Real.exp (-beta * E (k + 1) a) * T k a b = Real.exp (-beta * E (k + 1) b) * T k b a

/-- The Gibbs (heat-bath) relaxation kernel for the energy function `E (k+1)`. -/
noncomputable def gibbsKernel (E : ℕ → X → ℝ) (beta : ℝ) (k : ℕ) (_a b : X) : ℝ :=
  Real.exp (-beta * E (k + 1) b) / partitionFn E beta (k + 1)

omit [Nonempty X] in
/-- The Gibbs kernels satisfy detailed balance, so the hypotheses of Crooks' theorem are
non-vacuous. -/
lemma gibbsKernel_detailedBalance (E : ℕ → X → ℝ) (beta : ℝ) :
    DetailedBalance E (gibbsKernel E beta) beta := by
  intro k a b
  simp only [gibbsKernel]
  ring

end Setup

section Proof

variable {X : Type*} [Fintype X] [Nonempty X]
variable {E : ℕ → X → ℝ} {T : ℕ → X → X → ℝ} {beta : ℝ} {N : ℕ} {x : ℕ → X}

omit [Fintype X] [Nonempty X] in
/-- The reversed product of kernels, reindexed. -/
lemma reverse_prod_eq :
    ∏ j ∈ Finset.range N, T (N - 1 - j) (reversePath N x j) (reversePath N x (j + 1))
      = ∏ k ∈ Finset.range N, T k (x (k + 1)) (x k) := by
  have h : ∀ j ∈ Finset.range N,
      T (N - 1 - j) (reversePath N x j) (reversePath N x (j + 1))
        = (fun k => T k (x (k + 1)) (x k)) (N - 1 - j) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have h1 : N - 1 - j + 1 = N - j := by omega
    have h2 : N - (j + 1) = N - 1 - j := by omega
    simp only [reversePath, h1, h2]
  rw [Finset.prod_congr rfl h]
  exact Finset.prod_range_reflect (fun k => T k (x (k + 1)) (x k)) N

omit [Fintype X] [Nonempty X] in
/-- Microscopic reversibility for the kernel product. -/
lemma prod_reverse_kernels (hDB : DetailedBalance E T beta) :
    ∏ k ∈ Finset.range N, T k (x (k + 1)) (x k)
      = (∏ k ∈ Finset.range N, T k (x k) (x (k + 1))) *
        Real.exp (-beta * ∑ k ∈ Finset.range N,
          (E (k + 1) (x k) - E (k + 1) (x (k + 1)))) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ, ih]
      have hb := hDB n (x n) (x (n + 1))
      have hkey : T n (x (n + 1)) (x n)
          = T n (x n) (x (n + 1)) *
            Real.exp (-beta * (E (n + 1) (x n) - E (n + 1) (x (n + 1)))) := by
        have hpos : (0 : ℝ) < Real.exp (-beta * E (n + 1) (x (n + 1))) := Real.exp_pos _
        have hd : Real.exp (-beta * (E (n + 1) (x n) - E (n + 1) (x (n + 1))))
            = Real.exp (-beta * E (n + 1) (x n))
              / Real.exp (-beta * E (n + 1) (x (n + 1))) := by
          rw [← Real.exp_sub]; ring_nf
        rw [hd, mul_div_assoc', eq_div_iff hpos.ne']
        linarith [hb]
      rw [hkey, mul_add, Real.exp_add]
      ring

omit [Fintype X] [Nonempty X] in
/-- Telescoping identity relating the detailed-balance exponent to the work. -/
lemma sum_energy_telescope :
    ∑ k ∈ Finset.range N, (E (k + 1) (x k) - E (k + 1) (x (k + 1)))
      = work E N x + E 0 (x 0) - E N (x N) := by
  have h : ∀ k, E (k + 1) (x k) - E (k + 1) (x (k + 1))
      = (E (k + 1) (x k) - E k (x k)) + (E k (x k) - E (k + 1) (x (k + 1))) := by
    intro k; ring
  simp only [h, Finset.sum_add_distrib]
  have h2 : ∑ k ∈ Finset.range N, ((fun k => E k (x k)) k - (fun k => E k (x k)) (k + 1))
      = E 0 (x 0) - E N (x N) := Finset.sum_range_sub' (fun k => E k (x k)) N
  rw [work]
  simp only at h2
  rw [h2]
  ring

/-- **Crooks fluctuation theorem** (product form): the forward path weight equals
`e^{β(W − ΔF)}` times the weight of the time-reversed path under the reversed protocol. -/
theorem crooks_theorem_mul (hDB : DetailedBalance E T beta) (hbeta : beta ≠ 0) :
    forwardProb E T beta N x
      = Real.exp (beta * (work E N x - freeEnergyDiff E beta N)) *
          reverseProb E T beta N (reversePath N x) := by
  have hZ0 := partitionFn_pos E beta 0
  have hZN := partitionFn_pos E beta N
  have hexp := exp_neg_beta_freeEnergyDiff E beta N hbeta
  have h0 : reversePath N x 0 = x N := by simp [reversePath]
  rw [reverseProb, h0, reverse_prod_eq, prod_reverse_kernels hDB, sum_energy_telescope]
  rw [forwardProb]
  have hsplit : Real.exp (beta * (work E N x - freeEnergyDiff E beta N))
      = Real.exp (beta * work E N x) * Real.exp (-beta * freeEnergyDiff E beta N) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, hexp]
  have hE : Real.exp (-beta * (work E N x + E 0 (x 0) - E N (x N)))
      = (Real.exp (beta * work E N x))⁻¹ *
        (Real.exp (-beta * E 0 (x 0)) * (Real.exp (-beta * E N (x N)))⁻¹) := by
    rw [← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hE]
  field_simp

/-- **Crooks fluctuation theorem**: `P_F(γ) / P_R(γ̄) = e^{β(W(γ) − ΔF)}`,
for a microscopically reversible (detailed-balance) protocol on a finite state space. -/
theorem crooks_theorem (hDB : DetailedBalance E T beta) (hbeta : beta ≠ 0)
    (hne : reverseProb E T beta N (reversePath N x) ≠ 0) :
    forwardProb E T beta N x / reverseProb E T beta N (reversePath N x)
      = Real.exp (beta * (work E N x - freeEnergyDiff E beta N)) := by
  rw [crooks_theorem_mul hDB hbeta, mul_div_assoc, div_self hne, mul_one]

end Proof

/-- Coarse-grained form of Crooks' theorem: summing the path-level identity over all
trajectories with a given work value `w` gives `P_F(w) = e^{β(w − ΔF)} P_R(−w)`. -/
theorem crooks_work_distribution {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (R : Γ → Γ) (hR : Function.Involutive R) (W : Γ → ℝ) (hW : ∀ g, W (R g) = -W g)
    (pF pR : Γ → ℝ) (beta dF w : ℝ)
    (h : ∀ g, pF g = Real.exp (beta * (W g - dF)) * pR (R g)) :
    ∑ g ∈ Finset.univ.filter (fun g => W g = w), pF g
      = Real.exp (beta * (w - dF)) *
          ∑ g ∈ Finset.univ.filter (fun g => W g = -w), pR g := by
  classical
  have step1 : ∑ g ∈ Finset.univ.filter (fun g => W g = w), pF g
      = Real.exp (beta * (w - dF)) *
        ∑ g ∈ Finset.univ.filter (fun g => W g = w), pR (R g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro g hg
    simp only [Finset.mem_filter] at hg
    rw [h g, hg.2]
  rw [step1]
  congr 1
  refine Finset.sum_nbij' (fun g => R g) (fun g => R g) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [hW, hg]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [hW, hg]; ring
  · intro g _; exact hR g
  · intro g _; exact hR g
  · intro g _; rfl

end Phys

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

