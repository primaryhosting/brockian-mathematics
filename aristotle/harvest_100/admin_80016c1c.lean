import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Statement: Crooks fluctuation theorem: P_F(W)/P_R(−W) = e^{β(W−ΔF)}.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real
open scoped Classical

namespace Phys

variable {S : Type*} [Fintype S] [Nonempty S] {N : ℕ}

/-- `pt x k` is the state of the trajectory `x` (of length `N + 1`) at time `k`. -/
def pt (x : Fin (N + 1) → S) (k : ℕ) : S := x (Fin.ofNat (N + 1) k)

/-- Time reversal of a trajectory. -/
def revPath (x : Fin (N + 1) → S) : Fin (N + 1) → S := fun i => x i.rev

omit [Fintype S] [Nonempty S] in
@[simp] lemma revPath_revPath (x : Fin (N + 1) → S) : revPath (revPath x) = x := by
  funext i; simp [revPath]

omit [Fintype S] [Nonempty S] in
lemma pt_revPath (x : Fin (N + 1) → S) {k : ℕ} (hk : k ≤ N) :
    pt (revPath x) k = pt x (N - k) := by
  have h1 : ((Fin.ofNat (N + 1) k : Fin (N + 1)) : ℕ) = k := by
    simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : ((Fin.ofNat (N + 1) (N - k) : Fin (N + 1)) : ℕ) = N - k := by
    simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h3 : Fin.rev (Fin.ofNat (N + 1) k) = Fin.ofNat (N + 1) (N - k) := by
    apply Fin.ext
    rw [Fin.val_rev, h1, h2]
    omega
  show x (Fin.rev (Fin.ofNat (N + 1) k)) = x (Fin.ofNat (N + 1) (N - k))
  rw [h3]

/-- A discrete-time driven Markov process: a protocol of Hamiltonians `E k` together with
transition kernels `K k` obeying detailed balance with respect to the Gibbs measure of `E (k+1)`
at inverse temperature `beta`. -/
structure Setup (S : Type*) [Fintype S] (N : ℕ) where
  /-- inverse temperature -/
  beta : ℝ
  beta_pos : 0 < beta
  /-- the energy function at protocol step `k` -/
  E : ℕ → S → ℝ
  /-- the transition kernel used in the `k`-th relaxation step -/
  K : ℕ → S → S → ℝ
  K_pos : ∀ k x y, 0 < K k x y
  detailed_balance : ∀ k x y,
    Real.exp (-beta * E (k + 1) x) * K k x y = Real.exp (-beta * E (k + 1) y) * K k y x

namespace Setup

variable (P : Setup S N)

/-- Partition function of the Hamiltonian at protocol step `k`. -/
noncomputable def Z (k : ℕ) : ℝ := ∑ s : S, Real.exp (-P.beta * P.E k s)

/-- Gibbs (equilibrium) distribution of the Hamiltonian at protocol step `k`. -/
noncomputable def gibbs (k : ℕ) (s : S) : ℝ := Real.exp (-P.beta * P.E k s) / P.Z k

/-- Free energy difference between the final and the initial equilibrium states. -/
noncomputable def deltaF : ℝ := -(1 / P.beta) * Real.log (P.Z N / P.Z 0)

/-- Work performed on the system along a forward trajectory: at each step the Hamiltonian is
switched from `E k` to `E (k+1)` while the system sits in state `x k`. -/
def work (x : Fin (N + 1) → S) : ℝ :=
  ∑ k ∈ range N, (P.E (k + 1) (pt x k) - P.E k (pt x k))

/-- Work performed along a trajectory of the reverse process.  In the reverse process the
protocol is run backwards, `E N, E (N-1), …, E 0`, and each Hamiltonian switch happens *after*
the corresponding relaxation step. -/
def workRev (y : Fin (N + 1) → S) : ℝ :=
  ∑ k ∈ range N, (P.E (N - (k + 1)) (pt y (k + 1)) - P.E (N - k) (pt y (k + 1)))

/-- Probability of a forward trajectory: equilibrium start followed by the kernels `K 0, …`. -/
noncomputable def pathF (x : Fin (N + 1) → S) : ℝ :=
  P.gibbs 0 (pt x 0) * ∏ k ∈ range N, P.K k (pt x k) (pt x (k + 1))

/-- Probability of a trajectory of the reverse process: it starts from the equilibrium state of
`E N` and uses the kernels in reversed order `K (N-1), K (N-2), …`. -/
noncomputable def pathR (y : Fin (N + 1) → S) : ℝ :=
  P.gibbs N (pt y 0) * ∏ k ∈ range N, P.K (N - (k + 1)) (pt y k) (pt y (k + 1))

/-- Forward work distribution `P_F(w)`. -/
noncomputable def PF (w : ℝ) : ℝ :=
  ∑ x ∈ univ.filter (fun x : Fin (N + 1) → S => P.work x = w), P.pathF x

/-- Reverse work distribution `P_R(w)`. -/
noncomputable def PR (w : ℝ) : ℝ :=
  ∑ y ∈ univ.filter (fun y : Fin (N + 1) → S => P.workRev y = w), P.pathR y

lemma Z_pos (k : ℕ) : 0 < P.Z k :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

lemma gibbs_pos (k : ℕ) (s : S) : 0 < P.gibbs k s :=
  div_pos (Real.exp_pos _) (P.Z_pos k)

lemma pathR_pos (y : Fin (N + 1) → S) : 0 < P.pathR y :=
  mul_pos (P.gibbs_pos _ _) (Finset.prod_pos fun _ _ => P.K_pos _ _ _)

omit [Nonempty S] in
lemma workRev_revPath (x : Fin (N + 1) → S) : P.workRev (revPath x) = -P.work x := by
  rw [workRev, work, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_range_reflect (fun j => -(P.E (j + 1) (pt x j) - P.E j (pt x j))) N]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < N := Finset.mem_range.mp hk
  have h1 : pt (revPath x) (k + 1) = pt x (N - (k + 1)) := pt_revPath x (by omega)
  have h2 : N - 1 - k + 1 = N - k := by omega
  have h3 : N - 1 - k = N - (k + 1) := by omega
  rw [h1, h2, h3]
  ring

omit [Nonempty S] in
lemma pathR_revPath (x : Fin (N + 1) → S) :
    P.pathR (revPath x)
      = P.gibbs N (pt x N) * ∏ k ∈ range N, P.K k (pt x (k + 1)) (pt x k) := by
  rw [pathR]
  congr 1
  · rw [pt_revPath x (Nat.zero_le N), Nat.sub_zero]
  · rw [← Finset.prod_range_reflect (fun j => P.K j (pt x (j + 1)) (pt x j)) N]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < N := Finset.mem_range.mp hk
    have h1 : pt (revPath x) k = pt x (N - k) := pt_revPath x (by omega)
    have h2 : pt (revPath x) (k + 1) = pt x (N - (k + 1)) := pt_revPath x (by omega)
    have h3 : N - 1 - k + 1 = N - k := by omega
    have h4 : N - 1 - k = N - (k + 1) := by omega
    rw [h1, h2, h3, h4]

omit [Nonempty S] in
lemma kernel_ratio (k : ℕ) (a b : S) :
    P.K k a b = Real.exp (P.beta * (P.E (k + 1) a - P.E (k + 1) b)) * P.K k b a := by
  apply mul_left_cancel₀ (Real.exp_ne_zero (-P.beta * P.E (k + 1) a))
  rw [← mul_assoc, ← Real.exp_add]
  have h : -P.beta * P.E (k + 1) a + P.beta * (P.E (k + 1) a - P.E (k + 1) b)
      = -P.beta * P.E (k + 1) b := by ring
  rw [h, P.detailed_balance k a b]

omit [Nonempty S] in
lemma prod_forward (x : Fin (N + 1) → S) :
    ∏ k ∈ range N, P.K k (pt x k) (pt x (k + 1))
      = Real.exp (P.beta * ∑ k ∈ range N,
          (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1))))
        * ∏ k ∈ range N, P.K k (pt x (k + 1)) (pt x k) := by
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => P.kernel_ratio k _ _

omit [Nonempty S] in
lemma work_telescope (x : Fin (N + 1) → S) :
    P.work x - ∑ k ∈ range N, (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1)))
      = P.E N (pt x N) - P.E 0 (pt x 0) := by
  rw [work, ← Finset.sum_sub_distrib]
  have h : ∀ k ∈ range N,
      (P.E (k + 1) (pt x k) - P.E k (pt x k))
        - (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1)))
      = (fun j => P.E j (pt x j)) (k + 1) - (fun j => P.E j (pt x j)) k := by
    intro k _; ring
  rw [Finset.sum_congr rfl h]
  exact Finset.sum_range_sub (fun j => P.E j (pt x j)) N

lemma exp_beta_deltaF : Real.exp (P.beta * P.deltaF) = P.Z 0 / P.Z N := by
  have hb : P.beta ≠ 0 := ne_of_gt P.beta_pos
  have h1 : P.beta * P.deltaF = -Real.log (P.Z N / P.Z 0) := by
    rw [deltaF]; field_simp
  rw [h1, Real.exp_neg, Real.exp_log (div_pos (P.Z_pos N) (P.Z_pos 0)), inv_div]

/-- **Microscopic reversibility**: the ratio of the probability of a forward trajectory to that of
its time reverse under the reverse protocol is `exp (β (W - ΔF))`. -/
theorem pathF_eq_exp_mul_pathR (x : Fin (N + 1) → S) :
    P.pathF x = Real.exp (P.beta * (P.work x - P.deltaF)) * P.pathR (revPath x) := by
  have hZ0 : (0:ℝ) < P.Z 0 := P.Z_pos 0
  have hZN : (0:ℝ) < P.Z N := P.Z_pos N
  have hdF : Real.exp (P.beta * (P.work x - P.deltaF))
      = Real.exp (P.beta * P.work x) * (P.Z N / P.Z 0) := by
    rw [mul_sub, Real.exp_sub, P.exp_beta_deltaF]
    field_simp
  have hexp : Real.exp (-P.beta * P.E 0 (pt x 0))
        * Real.exp (P.beta * ∑ k ∈ range N,
            (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1))))
      = Real.exp (P.beta * P.work x) * Real.exp (-P.beta * P.E N (pt x N)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-P.beta) * P.work_telescope x
  rw [pathF, P.pathR_revPath x, gibbs, gibbs, P.prod_forward x, hdF]
  simp only [neg_mul] at hexp ⊢
  set A := ∏ k ∈ range N, P.K k (pt x (k + 1)) (pt x k) with hA
  set e := Real.exp (P.beta * ∑ k ∈ range N,
      (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1)))) with he
  field_simp
  linear_combination A * hexp

/-- Auxiliary: the reverse work distribution at `-w` is strictly positive as soon as some
trajectory realises the work value `w`. -/
lemma PR_pos (w : ℝ) (h : ∃ x : Fin (N + 1) → S, P.work x = w) : 0 < P.PR (-w) := by
  obtain ⟨x, hx⟩ := h
  refine Finset.sum_pos (fun y _ => P.pathR_pos y) ⟨revPath x, ?_⟩
  simp [Finset.mem_filter, P.workRev_revPath x, hx]

omit [Nonempty S] in
/-- Reindexing the forward trajectories with work `w` by time reversal. -/
lemma sum_pathR_revPath (w : ℝ) :
    ∑ x ∈ univ.filter (fun x : Fin (N + 1) → S => P.work x = w), P.pathR (revPath x)
      = ∑ y ∈ univ.filter (fun y : Fin (N + 1) → S => P.workRev y = -w), P.pathR y := by
  refine Finset.sum_nbij' (i := revPath) (j := revPath) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hw : P.work x = w := by simpa using (Finset.mem_filter.mp hx).2
    simp [Finset.mem_filter, P.workRev_revPath x, hw]
  · intro y hy
    have hw : P.workRev y = -w := by simpa using (Finset.mem_filter.mp hy).2
    have hrr := P.workRev_revPath (revPath y)
    rw [revPath_revPath] at hrr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith
  · intro x _; simp
  · intro y _; simp
  · intro x _; rfl

/-- Crooks fluctuation theorem, product form: `P_F(W) = e^{β(W-ΔF)} P_R(-W)`. -/
theorem crooks_mul (w : ℝ) :
    P.PF w = Real.exp (P.beta * (w - P.deltaF)) * P.PR (-w) := by
  have h1 : P.PF w
      = ∑ x ∈ univ.filter (fun x : Fin (N + 1) → S => P.work x = w),
          Real.exp (P.beta * (w - P.deltaF)) * P.pathR (revPath x) := by
    rw [PF]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hw : P.work x = w := by simpa using (Finset.mem_filter.mp hx).2
    rw [P.pathF_eq_exp_mul_pathR x, hw]
  rw [h1, ← Finset.mul_sum, P.sum_pathR_revPath w, PR]

end Setup

section Examples

/-- The theorem is not vacuous: for an arbitrary protocol of Hamiltonians `E` the *heat-bath*
(full re-equilibration) kernels satisfy the required detailed balance condition. -/
noncomputable def heatBath (N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (E : ℕ → S → ℝ) :
    Setup S N where
  beta := beta
  beta_pos := hbeta
  E := E
  K := fun k _ y => Real.exp (-beta * E (k + 1) y) / ∑ s : S, Real.exp (-beta * E (k + 1) s)
  K_pos := fun k _ _ =>
    div_pos (Real.exp_pos _) (Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty)
  detailed_balance := fun k x y => by ring

/-- The heat-bath kernels are genuine stochastic matrices. -/
lemma heatBath_stochastic (N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (E : ℕ → S → ℝ)
    (k : ℕ) (x : S) : ∑ y : S, (heatBath N beta hbeta E).K k x y = 1 := by
  have hZ : (0:ℝ) < ∑ s : S, Real.exp (-beta * E (k + 1) s) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  simp only [heatBath, ← Finset.sum_div]
  exact div_self (ne_of_gt hZ)

end Examples

/-- **Crooks fluctuation theorem**: for every work value `w` that is realised by some
trajectory, the ratio of the forward work distribution at `w` and the reverse work distribution
at `-w` equals `e^{β(W-ΔF)}`. -/
theorem crooks_theorem (P : Setup S N) (w : ℝ) (h : ∃ x : Fin (N + 1) → S, P.work x = w) :
    P.PF w / P.PR (-w) = Real.exp (P.beta * (w - P.deltaF)) := by
  have hpos := P.PR_pos w h
  rw [P.crooks_mul w]
  field_simp

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

