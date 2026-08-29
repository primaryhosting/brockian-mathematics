import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-!
## Setup

We formalise the discrete-time (Crooks 1998) setting.

A *protocol* of `N` steps on a finite state space `S` consists of

* a family of energy functions `E 0, E 1, …, E N : S → ℝ` (the externally controlled
  Hamiltonian at each protocol stage), and
* a family of stochastic kernels `T 0, T 1, …, T N : S → S → ℝ`, where `T k` describes
  the thermal relaxation of the system while the energy function is `E k`; each `T k`
  is assumed to satisfy *detailed balance* with respect to the Boltzmann weight of `E k`
  at inverse temperature `β`.

The **forward** experiment is: sample `x 0` from the equilibrium distribution of `E 0`;
then, for `k = 0, …, N-1`, first perform work by switching `E k ↦ E (k+1)` at frozen
configuration `x k` (this costs work `E (k+1) (x k) - E k (x k)`), and then let the system
relax `x k ↦ x (k+1)` using `T (k+1)`.

The **reverse** experiment runs the time-reversed protocol `Ẽ k = E (N - k)` with the
time-reversed kernels `T̃ k = T (N - k)`, starting from equilibrium of `Ẽ 0 = E N`, and with
each elementary step performed in the opposite order: first relax with `T̃ k`, then perform
the work `Ẽ k ↦ Ẽ (k+1)` at the (already relaxed) configuration.

This is the standard convention which makes the reverse of a forward trajectory a legal
reverse trajectory with exactly the opposite work.
-/

variable {S : Type*}

/-- Detailed balance of a kernel `K` with respect to the Boltzmann weight of the energy `E`
at inverse temperature `β`. -/
def DetailedBalance (β : ℝ) (E : S → ℝ) (K : S → S → ℝ) : Prop :=
  ∀ a b : S, Real.exp (-β * E a) * K a b = Real.exp (-β * E b) * K b a

/-- The canonical partition function `Z = ∑ₛ e^{-βE(s)}`. -/
noncomputable def partitionFunction [Fintype S] (β : ℝ) (E : S → ℝ) : ℝ :=
  ∑ s : S, Real.exp (-β * E s)

/-- The equilibrium free energy `F = -β⁻¹ log Z`. -/
noncomputable def freeEnergy [Fintype S] (β : ℝ) (E : S → ℝ) : ℝ :=
  -(1 / β) * Real.log (partitionFunction β E)

/-- The work performed along a forward trajectory: at step `k` the energy is switched from
`E k` to `E (k+1)` while the system sits in the configuration `x k`. -/
def workFwd (N : ℕ) (E : ℕ → S → ℝ) (x : ℕ → S) : ℝ :=
  ∑ k ∈ Finset.range N, (E (k + 1) (x k) - E k (x k))

/-- The work performed along a reverse-type trajectory: at step `k` the system first relaxes
from `x k` to `x (k+1)` and only then the energy is switched from `E k` to `E (k+1)`. -/
def workBwd (N : ℕ) (E : ℕ → S → ℝ) (x : ℕ → S) : ℝ :=
  ∑ k ∈ Finset.range N, (E (k + 1) (x (k + 1)) - E k (x (k + 1)))

/-- Probability weight of the trajectory `x` in the forward experiment
(work first, then relaxation). -/
noncomputable def fwdWeight [Fintype S] (β : ℝ) (N : ℕ) (E : ℕ → S → ℝ)
    (T : ℕ → S → S → ℝ) (x : ℕ → S) : ℝ :=
  Real.exp (-β * E 0 (x 0)) / partitionFunction β (E 0) *
    ∏ k ∈ Finset.range N, T (k + 1) (x k) (x (k + 1))

/-- Probability weight of the trajectory `x` in a reverse-type experiment
(relaxation first, then work). -/
noncomputable def bwdWeight [Fintype S] (β : ℝ) (N : ℕ) (E : ℕ → S → ℝ)
    (T : ℕ → S → S → ℝ) (x : ℕ → S) : ℝ :=
  Real.exp (-β * E 0 (x 0)) / partitionFunction β (E 0) *
    ∏ k ∈ Finset.range N, T k (x k) (x (k + 1))

/-- The time-reversed protocol. -/
def revEnergy (N : ℕ) (E : ℕ → S → ℝ) : ℕ → S → ℝ := fun k => E (N - k)

/-- The time-reversed family of kernels. -/
def revKernel (N : ℕ) (T : ℕ → S → S → ℝ) : ℕ → S → S → ℝ := fun k => T (N - k)

/-- The time-reversed trajectory. -/
def revPath (N : ℕ) (x : ℕ → S) : ℕ → S := fun k => x (N - k)

lemma revEnergy_detailedBalance (β : ℝ) (N : ℕ) (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ)
    (hDB : ∀ k, DetailedBalance β (E k) (T k)) (k : ℕ) :
    DetailedBalance β (revEnergy N E k) (revKernel N T k) := hDB (N - k)

/-!
## Microscopic reversibility

The heart of the matter: an induction on the number of protocol steps.
-/

/-- **Microscopic reversibility.** For any trajectory `x`, the (unnormalised) forward weight
and the (unnormalised) weight of the reversed trajectory differ exactly by `e^{βW}`. -/
theorem micro_reversibility (β : ℝ) (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ)
    (hDB : ∀ k, DetailedBalance β (E k) (T k)) (x : ℕ → S) (N : ℕ) :
    Real.exp (-β * E 0 (x 0)) * ∏ k ∈ Finset.range N, T (k + 1) (x k) (x (k + 1))
      = Real.exp (β * workFwd N E x) *
          (Real.exp (-β * E N (x N)) *
            ∏ k ∈ Finset.range N, T (k + 1) (x (k + 1)) (x k)) := by
  induction N with
  | zero => simp [workFwd]
  | succ N ih =>
      have hdb := hDB (N + 1) (x N) (x (N + 1))
      -- rewrite the new forward transition using detailed balance
      have hcancel : Real.exp (β * E (N + 1) (x N)) * Real.exp (-β * E (N + 1) (x N)) = 1 := by
        rw [← Real.exp_add]
        have : β * E (N + 1) (x N) + -β * E (N + 1) (x N) = 0 := by ring
        rw [this, Real.exp_zero]
      have key : T (N + 1) (x N) (x (N + 1))
          = Real.exp (β * E (N + 1) (x N)) *
              (Real.exp (-β * E (N + 1) (x (N + 1))) * T (N + 1) (x (N + 1)) (x N)) := by
        calc T (N + 1) (x N) (x (N + 1))
            = (Real.exp (β * E (N + 1) (x N)) * Real.exp (-β * E (N + 1) (x N))) *
                T (N + 1) (x N) (x (N + 1)) := by rw [hcancel, one_mul]
          _ = Real.exp (β * E (N + 1) (x N)) *
                (Real.exp (-β * E (N + 1) (x N)) * T (N + 1) (x N) (x (N + 1))) := by ring
          _ = Real.exp (β * E (N + 1) (x N)) *
                (Real.exp (-β * E (N + 1) (x (N + 1))) * T (N + 1) (x (N + 1)) (x N)) := by
              rw [hdb]
      have hwork : Real.exp (β * workFwd (N + 1) E x)
          = Real.exp (β * workFwd N E x) *
              (Real.exp (β * E (N + 1) (x N)) * Real.exp (-β * E N (x N))) := by
        rw [workFwd, Finset.sum_range_succ, ← workFwd, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [Finset.prod_range_succ, Finset.prod_range_succ, hwork, key]
      linear_combination (Real.exp (β * E (N + 1) (x N)) *
        Real.exp (-β * E (N + 1) (x (N + 1))) * T (N + 1) (x (N + 1)) (x N)) * ih

/-!
## Rewriting the reverse weight in terms of the forward trajectory
-/

lemma bwdWeight_revPath [Fintype S] (β : ℝ) (N : ℕ) (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ)
    (x : ℕ → S) :
    bwdWeight β N (revEnergy N E) (revKernel N T) (revPath N x)
      = Real.exp (-β * E N (x N)) / partitionFunction β (E N) *
          ∏ k ∈ Finset.range N, T (k + 1) (x (k + 1)) (x k) := by
  unfold bwdWeight
  have h1 : (revEnergy N E) 0 = E N := rfl
  have h2 : (revPath N x) 0 = x N := rfl
  rw [h1, h2]
  congr 1
  have hstep : ∀ k ∈ Finset.range N,
      revKernel N T k (revPath N x k) (revPath N x (k + 1))
        = (fun j => T (j + 1) (x (j + 1)) (x j)) (N - 1 - k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have e1 : N - 1 - k + 1 = N - k := by omega
    have e2 : N - (k + 1) = N - 1 - k := by omega
    simp only [revKernel, revPath, e1, e2]
  rw [Finset.prod_congr rfl hstep]
  exact Finset.prod_range_reflect (fun j => T (j + 1) (x (j + 1)) (x j)) N

lemma workBwd_revPath (N : ℕ) (E : ℕ → S → ℝ) (x : ℕ → S) :
    workBwd N (revEnergy N E) (revPath N x) = -workFwd N E x := by
  unfold workBwd workFwd
  rw [← Finset.sum_neg_distrib]
  have hstep : ∀ k ∈ Finset.range N,
      (revEnergy N E) (k + 1) ((revPath N x) (k + 1)) - (revEnergy N E) k ((revPath N x) (k + 1))
        = (fun j => -(E (j + 1) (x j) - E j (x j))) (N - 1 - k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have e2 : N - (k + 1) = N - 1 - k := by omega
    have e1 : N - 1 - k + 1 = N - k := by omega
    simp only [revEnergy, revPath, e2, e1]
    ring
  rw [Finset.sum_congr rfl hstep]
  exact Finset.sum_range_reflect (fun j => -(E (j + 1) (x j) - E j (x j))) N

/-!
## Crooks' relation at the level of single trajectories
-/

lemma partitionFunction_pos [Fintype S] [Nonempty S] (β : ℝ) (E : S → ℝ) :
    0 < partitionFunction β E := by
  unfold partitionFunction
  exact Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty

lemma exp_neg_beta_deltaF [Fintype S] [Nonempty S] {β : ℝ} (hβ : β ≠ 0) (E₀ E₁ : S → ℝ) :
    Real.exp (-β * (freeEnergy β E₁ - freeEnergy β E₀))
      = partitionFunction β E₁ / partitionFunction β E₀ := by
  have h0 : (0:ℝ) < partitionFunction β E₀ := partitionFunction_pos β E₀
  have h1 : (0:ℝ) < partitionFunction β E₁ := partitionFunction_pos β E₁
  have : -β * (freeEnergy β E₁ - freeEnergy β E₀)
      = Real.log (partitionFunction β E₁) - Real.log (partitionFunction β E₀) := by
    unfold freeEnergy
    field_simp
    ring
  rw [this, Real.exp_sub, Real.exp_log h1, Real.exp_log h0]

/-- **Crooks' relation for a single trajectory.** The probability of a forward trajectory and
the probability of its time reverse under the reversed protocol satisfy
`P_F(x) = e^{β(W - ΔF)} P_R(x̄)`. -/
theorem crooks_trajectory [Fintype S] [Nonempty S] {β : ℝ} (hβ : β ≠ 0) (N : ℕ)
    (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ) (hDB : ∀ k, DetailedBalance β (E k) (T k))
    (x : ℕ → S) :
    fwdWeight β N E T x
      = Real.exp (β * (workFwd N E x - (freeEnergy β (E N) - freeEnergy β (E 0)))) *
          bwdWeight β N (revEnergy N E) (revKernel N T) (revPath N x) := by
  have h0 : (0:ℝ) < partitionFunction β (E 0) := partitionFunction_pos β (E 0)
  have hN : (0:ℝ) < partitionFunction β (E N) := partitionFunction_pos β (E N)
  have hmicro := micro_reversibility β E T hDB x N
  have hdf := exp_neg_beta_deltaF hβ (E 0) (E N)
  have hsplit : Real.exp (β * (workFwd N E x - (freeEnergy β (E N) - freeEnergy β (E 0))))
      = Real.exp (β * workFwd N E x) *
          (partitionFunction β (E N) / partitionFunction β (E 0)) := by
    rw [← hdf, ← Real.exp_add]
    congr 1
    ring
  rw [bwdWeight_revPath, hsplit, fwdWeight]
  field_simp
  simp only [neg_mul] at hmicro ⊢
  linear_combination hmicro

/-!
## Coarse graining: the work distributions
-/

/-- Abstract coarse-graining step: a work-reversing involution on a finite trajectory space
turns a trajectory-wise identity into an identity between work distributions. -/
lemma sum_filter_involution {Ω : Type*} [Fintype Ω] (R : Ω → Ω) (hR : ∀ ω, R (R ω) = ω)
    (WF WR PF PR : Ω → ℝ) (g : ℝ → ℝ) (w : ℝ)
    (hW : ∀ ω, WR (R ω) = -WF ω)
    (hP : ∀ ω, PF ω = g (WF ω) * PR (R ω)) :
    ∑ ω ∈ Finset.univ.filter (fun ω => WF ω = w), PF ω
      = g w * ∑ η ∈ Finset.univ.filter (fun η => WR η = -w), PR η := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun ω => R ω) (j := fun η => R η) ?_ ?_ ?_ ?_ ?_
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [hW ω, hω]
  · intro η hη
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
    have : WR (R (R η)) = -WF (R η) := hW (R η)
    rw [hR η] at this
    rw [hη] at this
    linarith
  · intro ω _; exact hR ω
  · intro η _; exact hR η
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [hP ω, hω]

/-- The trajectory space of an `N`-step protocol: `N+1` successive configurations. -/
abbrev Traj (S : Type*) (N : ℕ) : Type _ := Fin (N + 1) → S

/-- A trajectory viewed as a function `ℕ → S` (constant past the final time). -/
def toPath {N : ℕ} (p : Traj S N) : ℕ → S := fun n => p ⟨min n N, by omega⟩

/-- Time reversal of a trajectory. -/
def revTraj {N : ℕ} (p : Traj S N) : Traj S N := fun i => p i.rev

lemma revTraj_involutive {N : ℕ} (p : Traj S N) : revTraj (revTraj p) = p := by
  funext i
  simp [revTraj]

lemma toPath_revTraj {N : ℕ} (p : Traj S N) : toPath (revTraj p) = revPath N (toPath p) := by
  funext n
  simp only [toPath, revTraj, revPath]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

/-- **Crooks fluctuation theorem.**

For a finite system in contact with a heat bath at inverse temperature `β`, driven by an
`N`-step protocol `E 0, …, E N` whose relaxation kernels `T k` satisfy detailed balance,
the forward work distribution `P_F` and the work distribution `P_R` of the time-reversed
protocol satisfy
`P_F(W) = e^{β (W - ΔF)} · P_R(-W)`,
where `ΔF = F(E N) - F(E 0)` is the equilibrium free-energy difference. -/
theorem crooks_theorem [Fintype S] [Nonempty S] [DecidableEq S] {β : ℝ} (hβ : β ≠ 0) (N : ℕ)
    (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ) (hDB : ∀ k, DetailedBalance β (E k) (T k)) (w : ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p : Traj S N => workFwd N E (toPath p) = w),
        fwdWeight β N E T (toPath p)
      = Real.exp (β * (w - (freeEnergy β (E N) - freeEnergy β (E 0)))) *
        ∑ q ∈ Finset.univ.filter
            (fun q : Traj S N => workBwd N (revEnergy N E) (toPath q) = -w),
          bwdWeight β N (revEnergy N E) (revKernel N T) (toPath q) := by
  classical
  refine sum_filter_involution (R := fun p : Traj S N => revTraj p) revTraj_involutive
    (WF := fun p => workFwd N E (toPath p))
    (WR := fun q => workBwd N (revEnergy N E) (toPath q))
    (PF := fun p => fwdWeight β N E T (toPath p))
    (PR := fun q => bwdWeight β N (revEnergy N E) (revKernel N T) (toPath q))
    (g := fun v => Real.exp (β * (v - (freeEnergy β (E N) - freeEnergy β (E 0))))) w ?_ ?_
  · intro p
    show workBwd N (revEnergy N E) (toPath (revTraj p)) = -workFwd N E (toPath p)
    rw [toPath_revTraj, workBwd_revPath]
  · intro p
    show fwdWeight β N E T (toPath p)
        = Real.exp (β * (workFwd N E (toPath p) -
            (freeEnergy β (E N) - freeEnergy β (E 0)))) *
          bwdWeight β N (revEnergy N E) (revKernel N T) (toPath (revTraj p))
    rw [toPath_revTraj]
    exact crooks_trajectory hβ N E T hDB (toPath p)

/-!
## Non-vacuity: the hypotheses are satisfiable

The Gibbs sampler (heat-bath) kernel for an energy `E` is a genuine stochastic matrix with
strictly positive entries satisfying detailed balance, so the family of hypotheses used in
`crooks_theorem` is realisable.
-/

/-- The heat-bath (Gibbs sampler) kernel associated with an energy function. -/
noncomputable def gibbsKernel [Fintype S] (β : ℝ) (E : S → ℝ) : S → S → ℝ :=
  fun _ b => Real.exp (-β * E b) / partitionFunction β E

lemma gibbsKernel_pos [Fintype S] [Nonempty S] (β : ℝ) (E : S → ℝ) (a b : S) :
    0 < gibbsKernel β E a b :=
  div_pos (Real.exp_pos _) (partitionFunction_pos β E)

lemma gibbsKernel_row_sum [Fintype S] [Nonempty S] (β : ℝ) (E : S → ℝ) (a : S) :
    ∑ b : S, gibbsKernel β E a b = 1 := by
  unfold gibbsKernel
  rw [← Finset.sum_div]
  exact div_self (partitionFunction_pos β E).ne'

lemma gibbsKernel_detailedBalance [Fintype S] (β : ℝ) (E : S → ℝ) :
    DetailedBalance β E (gibbsKernel β E) := by
  intro a b
  unfold gibbsKernel
  ring

/-- The ratio form of Crooks' theorem: `P_F(W) / P_R(-W) = e^{β(W - ΔF)}`. -/
theorem crooks_theorem_ratio [Fintype S] [Nonempty S] [DecidableEq S] {β : ℝ} (hβ : β ≠ 0)
    (N : ℕ) (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ) (hDB : ∀ k, DetailedBalance β (E k) (T k))
    (w : ℝ)
    (hpos : ∑ q ∈ Finset.univ.filter
        (fun q : Traj S N => workBwd N (revEnergy N E) (toPath q) = -w),
        bwdWeight β N (revEnergy N E) (revKernel N T) (toPath q) ≠ 0) :
    (∑ p ∈ Finset.univ.filter (fun p : Traj S N => workFwd N E (toPath p) = w),
        fwdWeight β N E T (toPath p)) /
      (∑ q ∈ Finset.univ.filter
          (fun q : Traj S N => workBwd N (revEnergy N E) (toPath q) = -w),
        bwdWeight β N (revEnergy N E) (revKernel N T) (toPath q))
      = Real.exp (β * (w - (freeEnergy β (E N) - freeEnergy β (E 0)))) := by
  rw [crooks_theorem hβ N E T hDB w]
  field_simp

end Phys

