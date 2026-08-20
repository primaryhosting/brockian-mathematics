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

/-- A driven microscopic system on a finite state space, observed at times
`0, 1, …, N`.

* `E k` is the energy function of the system after the `k`-th update of the
  external protocol parameter.
* `T k x y` is the probability that the thermalisation step performed while the
  energy function is `E k` takes the system from `x` to `y`.  It is assumed to
  satisfy *detailed balance* with respect to the Boltzmann weights of `E k` at
  inverse temperature `beta`.

A forward trajectory is a sequence of states `x₀, x₁, …, x_N`: the system starts
in thermal equilibrium for `E 0`, then alternately the protocol is advanced
(`E k → E (k+1)`, which costs work) and the system relaxes with the kernel
`T (k+1)`. -/
structure CrooksSystem where
  /-- the (finite, nonempty) microscopic state space -/
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  [neS : Nonempty S]
  /-- number of protocol steps -/
  N : ℕ
  /-- inverse temperature -/
  beta : ℝ
  beta_pos : 0 < beta
  /-- energy function after `k` protocol updates -/
  E : ℕ → S → ℝ
  /-- thermalisation kernel used while the energy is `E k` -/
  T : ℕ → S → S → ℝ
  /-- detailed balance of `T k` with respect to the Boltzmann weights of `E k` -/
  detailed_balance : ∀ (k : ℕ) (x y : S),
    Real.exp (-beta * E k x) * T k x y = Real.exp (-beta * E k y) * T k y x

attribute [instance] CrooksSystem.finS CrooksSystem.decS CrooksSystem.neS

variable (C : CrooksSystem)

/-- Partition function of the equilibrium state with energy `E k`. -/
noncomputable def partition (k : ℕ) : ℝ := ∑ x : C.S, Real.exp (-C.beta * C.E k x)

/-- Free energy difference between the initial and the final equilibrium state,
`ΔF = -(1/β) log (Z_N / Z_0)`. -/
noncomputable def deltaF : ℝ :=
  -(1 / C.beta) * Real.log (partition C C.N / partition C 0)

/-- The work performed on the system along the forward trajectory `γ`: at time
`k` the protocol is advanced while the system sits in the state `γ k`. -/
noncomputable def work (γ : ℕ → C.S) : ℝ :=
  ∑ k ∈ Finset.range C.N, (C.E (k + 1) (γ k) - C.E k (γ k))

/-- The work performed on the system along a trajectory `δ` of the *reverse*
process.  The reverse protocol runs through the energies `Ẽ k = E (N - k)`, and
each protocol update is performed after the corresponding relaxation step,
i.e. while the system sits in the state `δ (k+1)`. -/
noncomputable def workR (δ : ℕ → C.S) : ℝ :=
  ∑ k ∈ Finset.range C.N,
    (C.E (C.N - (k + 1)) (δ (k + 1)) - C.E (C.N - k) (δ (k + 1)))

/-- Probability of the forward trajectory `γ`: equilibrium weight of the initial
state times the transition probabilities. -/
noncomputable def probF (γ : ℕ → C.S) : ℝ :=
  Real.exp (-C.beta * C.E 0 (γ 0)) / partition C 0 *
    ∏ k ∈ Finset.range C.N, C.T (k + 1) (γ k) (γ (k + 1))

/-- Probability of the trajectory `δ` in the reverse process: the system starts
in equilibrium for the final energy `E N` and is driven with the reversed
protocol, so that the kernel used in its `(k+1)`-st step is `T (N - k)`. -/
noncomputable def probR (δ : ℕ → C.S) : ℝ :=
  Real.exp (-C.beta * C.E C.N (δ 0)) / partition C C.N *
    ∏ k ∈ Finset.range C.N, C.T (C.N - k) (δ k) (δ (k + 1))

/-- Trajectories, recorded as the list of the `N + 1` visited states. -/
abbrev Path : Type := Fin (C.N + 1) → C.S

/-- A trajectory viewed as a sequence indexed by `ℕ` (clamped past time `N`). -/
def toFun (p : Path C) : ℕ → C.S := fun k => p ⟨min k C.N, by omega⟩

/-- Time reversal of a trajectory. -/
def revPath (p : Path C) : Path C := fun i => p i.rev

/-- The forward work distribution: total probability of the forward
trajectories along which the work equals `w`. -/
noncomputable def distF (w : ℝ) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Path C => work C (toFun C p) = w),
    probF C (toFun C p)

/-- The reverse work distribution: total probability of the reverse-process
trajectories along which the work equals `w`. -/
noncomputable def distR (w : ℝ) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Path C => workR C (toFun C p) = w),
    probR C (toFun C p)

/-! ### Basic positivity facts -/

theorem partition_pos (k : ℕ) : 0 < partition C k :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem exp_neg_beta_deltaF :
    Real.exp (-(C.beta * deltaF C)) = partition C C.N / partition C 0 := by
  have hb : C.beta ≠ 0 := ne_of_gt C.beta_pos
  have hr : 0 < partition C C.N / partition C 0 :=
    div_pos (partition_pos C C.N) (partition_pos C 0)
  have : -(C.beta * deltaF C) = Real.log (partition C C.N / partition C 0) := by
    unfold deltaF
    field_simp
  rw [this, Real.exp_log hr]

/-! ### The key intermediate lemma: microscopic reversibility -/

/-- Telescoping identity relating the energy changes along a trajectory to the
work performed on it. -/
theorem sum_energy_diff (γ : ℕ → C.S) :
    ∑ k ∈ Finset.range C.N, (C.E (k + 1) (γ k) - C.E (k + 1) (γ (k + 1)))
      = work C γ + C.E 0 (γ 0) - C.E C.N (γ C.N) := by
  have key : ∑ k ∈ Finset.range C.N,
      (C.E k (γ k) - C.E (k + 1) (γ (k + 1))) = C.E 0 (γ 0) - C.E C.N (γ C.N) :=
    Finset.sum_range_sub' (fun k => C.E k (γ k)) C.N
  have split : ∑ k ∈ Finset.range C.N, (C.E (k + 1) (γ k) - C.E (k + 1) (γ (k + 1)))
      = (∑ k ∈ Finset.range C.N, (C.E (k + 1) (γ k) - C.E k (γ k)))
        + ∑ k ∈ Finset.range C.N, (C.E k (γ k) - C.E (k + 1) (γ (k + 1))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [split, key]
  unfold work
  ring

/-- Reversing a trajectory reverses the order of the transition probabilities. -/
theorem prod_rev (γ : ℕ → C.S) :
    ∏ k ∈ Finset.range C.N, C.T (C.N - k) (γ (C.N - k)) (γ (C.N - (k + 1)))
      = ∏ k ∈ Finset.range C.N, C.T (k + 1) (γ (k + 1)) (γ k) := by
  rw [← Finset.prod_range_reflect (fun j => C.T (j + 1) (γ (j + 1)) (γ j)) C.N]
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hk' : k < C.N := Finset.mem_range.mp hk
  have h1 : C.N - 1 - k + 1 = C.N - k := by omega
  have h2 : C.N - 1 - k = C.N - (k + 1) := by omega
  rw [h1, h2]

/-- **Microscopic reversibility.**  The probability of a forward trajectory and
the probability of its time reverse in the reverse process are related by
`P_F(γ) = e^{β (W(γ) - ΔF)} · P_R(γ̃)`. -/
theorem microscopic_reversibility (γ : ℕ → C.S) :
    probF C γ
      = Real.exp (C.beta * (work C γ - deltaF C)) * probR C (fun k => γ (C.N - k)) := by
  have hZ0 : partition C 0 ≠ 0 := (partition_pos C 0).ne'
  have hZN : partition C C.N ≠ 0 := (partition_pos C C.N).ne'
  -- detailed balance in ratio form
  have hDB : ∀ (k : ℕ) (x y : C.S),
      C.T k x y = Real.exp (C.beta * (C.E k x - C.E k y)) * C.T k y x := by
    intro k x y
    have hx : Real.exp (-C.beta * C.E k x) ≠ 0 := (Real.exp_pos _).ne'
    refine mul_left_cancel₀ hx ?_
    rw [C.detailed_balance k x y, ← mul_assoc, ← Real.exp_add]
    ring_nf
  -- rewrite the forward product in terms of the backward one
  have hprod : ∏ k ∈ Finset.range C.N, C.T (k + 1) (γ k) (γ (k + 1))
      = (∏ k ∈ Finset.range C.N,
          Real.exp (C.beta * (C.E (k + 1) (γ k) - C.E (k + 1) (γ (k + 1)))))
        * ∏ k ∈ Finset.range C.N, C.T (k + 1) (γ (k + 1)) (γ k) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => hDB _ _ _)
  have hexpprod : (∏ k ∈ Finset.range C.N,
      Real.exp (C.beta * (C.E (k + 1) (γ k) - C.E (k + 1) (γ (k + 1)))))
      = Real.exp (C.beta * (work C γ + C.E 0 (γ 0) - C.E C.N (γ C.N))) := by
    rw [← Real.exp_sum, ← Finset.mul_sum, sum_energy_diff C γ]
  have hexp : Real.exp (C.beta * (work C γ - deltaF C))
      = Real.exp (C.beta * work C γ) * (partition C C.N / partition C 0) := by
    rw [← exp_neg_beta_deltaF C, ← Real.exp_add]
    ring_nf
  have e1 : Real.exp (C.beta * (work C γ + C.E 0 (γ 0) - C.E C.N (γ C.N)))
      * Real.exp (-(C.beta * C.E 0 (γ 0)))
      = Real.exp (C.beta * work C γ) * Real.exp (-(C.beta * C.E C.N (γ C.N))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  unfold probF probR
  simp only [Nat.sub_zero]
  rw [prod_rev C γ, hprod, hexpprod, hexp]
  field_simp
  linear_combination (∏ k ∈ Finset.range C.N, C.T (k + 1) (γ (k + 1)) (γ k)) * e1

/-! ### Work of the reversed trajectory -/

theorem workR_rev (γ : ℕ → C.S) :
    workR C (fun k => γ (C.N - k)) = -work C γ := by
  calc workR C (fun k => γ (C.N - k))
      = ∑ k ∈ Finset.range C.N,
          ((fun j => C.E j (γ j) - C.E (j + 1) (γ j)) (C.N - 1 - k)) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk' : k < C.N := Finset.mem_range.mp hk
        have h1 : C.N - (k + 1) = C.N - 1 - k := by omega
        have h2 : C.N - k = C.N - 1 - k + 1 := by omega
        simp only []
        rw [h1, h2]
    _ = ∑ j ∈ Finset.range C.N, (C.E j (γ j) - C.E (j + 1) (γ j)) :=
        Finset.sum_range_reflect (fun j => C.E j (γ j) - C.E (j + 1) (γ j)) C.N
    _ = -work C γ := by
        unfold work
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)

theorem toFun_revPath (p : Path C) :
    toFun C (revPath C p) = fun k => toFun C p (C.N - k) := by
  funext k
  simp only [toFun, revPath]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

theorem revPath_involutive (p : Path C) : revPath C (revPath C p) = p := by
  funext i
  simp [revPath]

/-! ### The Crooks fluctuation theorem -/

/-- **Crooks fluctuation theorem.**  For every value `w` of the work, the
forward work distribution and the reverse work distribution satisfy
`P_F(w) = e^{β (w - ΔF)} · P_R(-w)`, i.e. `P_F(W) / P_R(-W) = e^{β(W - ΔF)}`. -/
theorem crooks_theorem (w : ℝ) :
    distF C w = Real.exp (C.beta * (w - deltaF C)) * distR C (-w) := by
  have hwork : ∀ p : Path C,
      workR C (toFun C (revPath C p)) = -work C (toFun C p) := by
    intro p
    rw [toFun_revPath C p, workR_rev C (toFun C p)]
  unfold distF distR
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (revPath C) (revPath C) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [hwork p, hp]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    have := hwork (revPath C q)
    rw [revPath_involutive C q] at this
    rw [hq] at this
    linarith
  · intro p _
    exact revPath_involutive C p
  · intro q _
    exact revPath_involutive C q
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [toFun_revPath C p, microscopic_reversibility C (toFun C p), hp]

/-- The Crooks theorem in ratio form: whenever the reverse process produces the
work value `-w` with positive probability, the ratio of the two work
distributions is `e^{β (w - ΔF)}`. -/
theorem crooks_theorem_ratio (w : ℝ) (h : distR C (-w) ≠ 0) :
    distF C w / distR C (-w) = Real.exp (C.beta * (w - deltaF C)) := by
  rw [crooks_theorem C w, mul_div_assoc, div_self h, mul_one]

/-! ### The hypotheses are satisfiable

The assumptions of `CrooksSystem` are not vacuous: for any state space, protocol
and temperature the "full thermalisation" kernel, which resamples the state from
the instantaneous Boltzmann distribution, satisfies detailed balance and is a
genuine (row-stochastic) Markov kernel. -/

noncomputable def thermalSystem (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (E : ℕ → S → ℝ) : CrooksSystem where
  S := S
  N := N
  beta := beta
  beta_pos := hbeta
  E := E
  T := fun k _ y => Real.exp (-beta * E k y) / ∑ z : S, Real.exp (-beta * E k z)
  detailed_balance := by
    intro k x y
    ring

theorem thermalSystem_row_sum (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (E : ℕ → S → ℝ) (k : ℕ) (x : S) :
    ∑ y : S, (thermalSystem S N beta hbeta E).T k x y = 1 := by
  have hZ : (0 : ℝ) < ∑ z : S, Real.exp (-beta * E k z) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [thermalSystem, ← Finset.sum_div]
  exact div_self hZ.ne'

end Phys

