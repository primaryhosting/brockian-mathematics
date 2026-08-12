/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## Setting

A driven classical system with a finite state space `S` is observed at the `N + 1` times
`0, 1, …, N`.  The externally controlled protocol is encoded by the energy functions
`E k : S → ℝ` (`k : Fin (N+1)`), and the stochastic relaxation between consecutive times by
Markov weights `K k : S → S → ℝ` (`k : Fin N`), where `K k x y` is the weight of the jump
`x ↦ y` performed while the energy function is `E k.succ`.

The single physical input is *microscopic reversibility* (detailed balance) of each `K k`
with respect to the Boltzmann distribution of `E k.succ` at inverse temperature `β`.

A forward trajectory `x : Fin (N+1) → S` is drawn by sampling `x 0` from the equilibrium
distribution of `E 0` and then applying the kernels `K 0, K 1, …`.  The reverse experiment
starts from the equilibrium distribution of `E (Fin.last N)` and applies the same kernels in
the opposite order, `K (N-1), …, K 0`.

Work is the energy change performed at fixed state, heat the energy change caused by the
jumps.  The free energies are `F k = -β⁻¹ log (Z k)`.
-/

section

variable {S : Type*}

/-- Partition function of the energy function `E` at inverse temperature `beta`. -/
noncomputable def Zpart [Fintype S] (beta : ℝ) (E : S → ℝ) : ℝ :=
  ∑ x : S, Real.exp (-beta * E x)

/-- Equilibrium (Boltzmann–Gibbs) probability of the state `x` for the energy `E`. -/
noncomputable def eqProb [Fintype S] (beta : ℝ) (E : S → ℝ) (x : S) : ℝ :=
  Real.exp (-beta * E x) / Zpart beta E

variable {N : ℕ}

/-- Probability weight of the forward trajectory `x`: equilibrium initial condition for
`E 0`, followed by the transition weights `K 0, K 1, …, K (N-1)`. -/
noncomputable def Pfwd [Fintype S] (beta : ℝ) (E : Fin (N + 1) → S → ℝ)
    (K : Fin N → S → S → ℝ) (x : Fin (N + 1) → S) : ℝ :=
  eqProb beta (E 0) (x 0) * ∏ k : Fin N, K k (x k.castSucc) (x k.succ)

/-- Probability weight of the reverse trajectory `y`: equilibrium initial condition for
`E (Fin.last N)`, followed by the transition weights in reversed order
`K (N-1), …, K 1, K 0`. -/
noncomputable def Prev [Fintype S] (beta : ℝ) (E : Fin (N + 1) → S → ℝ)
    (K : Fin N → S → S → ℝ) (y : Fin (N + 1) → S) : ℝ :=
  eqProb beta (E (Fin.last N)) (y 0) * ∏ k : Fin N, K k.rev (y k.castSucc) (y k.succ)

/-- Work performed on the system along the forward trajectory `x`: at each step the energy
function is switched from `E k` to `E k.succ` while the system sits in the state
`x k.castSucc`. -/
def work (E : Fin (N + 1) → S → ℝ) (x : Fin (N + 1) → S) : ℝ :=
  ∑ k : Fin N, (E k.succ (x k.castSucc) - E k.castSucc (x k.castSucc))

/-- Heat absorbed by the system along the forward trajectory `x`: at each step the state
jumps from `x k.castSucc` to `x k.succ` at fixed energy function `E k.succ`. -/
def heat (E : Fin (N + 1) → S → ℝ) (x : Fin (N + 1) → S) : ℝ :=
  ∑ k : Fin N, (E k.succ (x k.succ) - E k.succ (x k.castSucc))

/-- Work performed on the system along a reverse trajectory `y`: the reverse protocol
switches the energy from `E k.rev.succ` to `E k.rev.castSucc` while the system sits in the
state `y k.succ`. -/
def workRev (E : Fin (N + 1) → S → ℝ) (y : Fin (N + 1) → S) : ℝ :=
  ∑ k : Fin N, (E k.rev.castSucc (y k.succ) - E k.rev.succ (y k.succ))

/-- Free-energy difference between the final and the initial equilibrium states. -/
noncomputable def deltaF [Fintype S] (beta : ℝ) (E : Fin (N + 1) → S → ℝ) : ℝ :=
  -(1 / beta) * Real.log (Zpart beta (E (Fin.last N)) / Zpart beta (E 0))

/-- Time reversal of a trajectory. -/
def revTraj (x : Fin (N + 1) → S) : Fin (N + 1) → S := fun k => x k.rev

/-- Detailed balance (microscopic reversibility) of the transition weights. -/
def DetailedBalance [Fintype S] (beta : ℝ) (E : Fin (N + 1) → S → ℝ)
    (K : Fin N → S → S → ℝ) : Prop :=
  ∀ (k : Fin N) (a b : S),
    K k a b * Real.exp (-beta * E k.succ a) = K k b a * Real.exp (-beta * E k.succ b)

end

section Lemmas

variable {S : Type*} [Fintype S] [Nonempty S] {N : ℕ}

lemma Zpart_pos (beta : ℝ) (E : S → ℝ) : 0 < Zpart beta E := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- Telescoping sum over `Fin N`. -/
lemma sum_fin_telescope : ∀ (N : ℕ) (g : Fin (N + 1) → ℝ),
    ∑ k : Fin N, (g k.succ - g k.castSucc) = g (Fin.last N) - g 0 := by
  intro N
  induction N with
  | zero => intro g; simp
  | succ N ih =>
    intro g
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i : Fin (N + 1) => g i.castSucc)
    simp only [Fin.succ_castSucc] at h ⊢
    rw [h]
    simp [Fin.succ_last]

omit [Fintype S] [Nonempty S] in
/-- First law of thermodynamics: work plus heat is the total energy change. -/
lemma work_add_heat (E : Fin (N + 1) → S → ℝ) (x : Fin (N + 1) → S) :
    work E x + heat E x = E (Fin.last N) (x (Fin.last N)) - E 0 (x 0) := by
  have h := sum_fin_telescope N (fun i => E i (x i))
  rw [work, heat, ← Finset.sum_add_distrib, ← h]
  refine Finset.sum_congr rfl (fun k _ => by ring)

omit [Fintype S] [Nonempty S] in
/-- Reversing a trajectory reverses the sign of the work. -/
lemma workRev_revTraj (E : Fin (N + 1) → S → ℝ) (x : Fin (N + 1) → S) :
    workRev E (revTraj x) = -work E x := by
  have h1 : ∀ k : Fin N,
      (E k.rev.castSucc (revTraj x k.succ) - E k.rev.succ (revTraj x k.succ))
        = (fun j : Fin N => -(E j.succ (x j.castSucc) - E j.castSucc (x j.castSucc))) k.rev := by
    intro k
    simp only [revTraj, Fin.rev_succ]
    ring
  have h2 := Equiv.sum_comp (Fin.revPerm (n := N))
    (fun j : Fin N => -(E j.succ (x j.castSucc) - E j.castSucc (x j.castSucc)))
  rw [workRev, work, ← Finset.sum_neg_distrib]
  exact Eq.trans (Finset.sum_congr rfl (fun k _ => h1 k)) h2

omit [Nonempty S] in
/-- Microscopic reversibility, in ratio form, along a whole trajectory. -/
lemma prod_fwd_eq (beta : ℝ) (E : Fin (N + 1) → S → ℝ) (K : Fin N → S → S → ℝ)
    (hDB : DetailedBalance beta E K) (x : Fin (N + 1) → S) :
    ∏ k : Fin N, K k (x k.castSucc) (x k.succ) =
      (∏ k : Fin N, K k (x k.succ) (x k.castSucc)) * Real.exp (-beta * heat E x) := by
  have hstep : ∀ k : Fin N, K k (x k.castSucc) (x k.succ) =
      K k (x k.succ) (x k.castSucc) *
        Real.exp (-beta * (E k.succ (x k.succ) - E k.succ (x k.castSucc))) := by
    intro k
    have h := hDB k (x k.castSucc) (x k.succ)
    have hpos : (0:ℝ) < Real.exp (-beta * E k.succ (x k.castSucc)) := Real.exp_pos _
    have hsplit : Real.exp (-beta * (E k.succ (x k.succ) - E k.succ (x k.castSucc)))
        = Real.exp (-beta * E k.succ (x k.succ)) /
            Real.exp (-beta * E k.succ (x k.castSucc)) := by
      rw [← Real.exp_sub]
      ring_nf
    rw [hsplit]
    field_simp
    simp only [neg_mul] at h ⊢
    linarith [h]
  calc ∏ k : Fin N, K k (x k.castSucc) (x k.succ)
      = ∏ k : Fin N, (K k (x k.succ) (x k.castSucc) *
          Real.exp (-beta * (E k.succ (x k.succ) - E k.succ (x k.castSucc)))) :=
        Finset.prod_congr rfl (fun k _ => hstep k)
    _ = (∏ k : Fin N, K k (x k.succ) (x k.castSucc)) *
          ∏ k : Fin N, Real.exp (-beta * (E k.succ (x k.succ) - E k.succ (x k.castSucc))) :=
        Finset.prod_mul_distrib
    _ = (∏ k : Fin N, K k (x k.succ) (x k.castSucc)) * Real.exp (-beta * heat E x) := by
        rw [← Real.exp_sum, heat, Finset.mul_sum]

omit [Nonempty S] in
/-- The weight of the time-reversed trajectory in the reverse experiment. -/
lemma Prev_revTraj (beta : ℝ) (E : Fin (N + 1) → S → ℝ) (K : Fin N → S → S → ℝ)
    (x : Fin (N + 1) → S) :
    Prev beta E K (revTraj x) =
      eqProb beta (E (Fin.last N)) (x (Fin.last N)) *
        ∏ k : Fin N, K k (x k.succ) (x k.castSucc) := by
  have h0 : revTraj x 0 = x (Fin.last N) := by simp [revTraj]
  rw [Prev, h0]
  congr 1
  have : ∀ k : Fin N, K k.rev (revTraj x k.castSucc) (revTraj x k.succ) =
      (fun j : Fin N => K j (x j.succ) (x j.castSucc)) k.rev := by
    intro k
    simp [revTraj, Fin.rev_castSucc, Fin.rev_succ]
  rw [Finset.prod_congr rfl (fun k _ => this k)]
  exact Equiv.prod_comp (Fin.revPerm) (fun j : Fin N => K j (x j.succ) (x j.castSucc))

/-- **Crooks relation, pathwise form.**  The probability of a forward trajectory and that of
its time reverse differ exactly by the exponential of the dissipated work. -/
theorem crooks_pathwise (beta : ℝ) (hbeta : beta ≠ 0) (E : Fin (N + 1) → S → ℝ)
    (K : Fin N → S → S → ℝ) (hDB : DetailedBalance beta E K) (x : Fin (N + 1) → S) :
    Pfwd beta E K x =
      Real.exp (beta * (work E x - deltaF beta E)) * Prev beta E K (revTraj x) := by
  have hZ0 : (0:ℝ) < Zpart beta (E 0) := Zpart_pos _ _
  have hZN : (0:ℝ) < Zpart beta (E (Fin.last N)) := Zpart_pos _ _
  have hF : Real.exp (-beta * deltaF beta E) =
      Zpart beta (E (Fin.last N)) / Zpart beta (E 0) := by
    rw [deltaF]
    have : -beta * (-(1 / beta) * Real.log (Zpart beta (E (Fin.last N)) / Zpart beta (E 0)))
        = Real.log (Zpart beta (E (Fin.last N)) / Zpart beta (E 0)) := by
      field_simp
    rw [this, Real.exp_log (by positivity)]
  have hfirst := work_add_heat E x
  rw [Pfwd, prod_fwd_eq beta E K hDB x, Prev_revTraj]
  rw [eqProb, eqProb]
  have hexp : Real.exp (beta * (work E x - deltaF beta E)) =
      Real.exp (beta * work E x) * (Zpart beta (E (Fin.last N)) / Zpart beta (E 0)) := by
    rw [← hF, ← Real.exp_add]
    ring_nf
  rw [hexp]
  have hQ : Real.exp (-beta * E 0 (x 0)) * Real.exp (-beta * heat E x) =
      Real.exp (beta * work E x) * Real.exp (-beta * E (Fin.last N) (x (Fin.last N))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-beta) * hfirst
  have habs : ∀ A B C D P Z0 ZN : ℝ, Z0 ≠ 0 → ZN ≠ 0 → A * B = C * D →
      A / Z0 * (P * B) = C * (ZN / Z0) * (D / ZN * P) := by
    intro A B C D P Z0 ZN h0 hN h
    field_simp
    linear_combination P * h
  exact habs _ _ _ _ _ _ _ hZ0.ne' hZN.ne' hQ

end Lemmas

section Main

variable {S : Type*} [Fintype S] [Nonempty S] {N : ℕ}

/-- Probability that the forward experiment produces work `w`. -/
noncomputable def PF (beta : ℝ) (E : Fin (N + 1) → S → ℝ) (K : Fin N → S → S → ℝ)
    (w : ℝ) : ℝ :=
  ∑ x : Fin (N + 1) → S, if work E x = w then Pfwd beta E K x else 0

/-- Probability that the reverse experiment produces work `w`. -/
noncomputable def PR (beta : ℝ) (E : Fin (N + 1) → S → ℝ) (K : Fin N → S → S → ℝ)
    (w : ℝ) : ℝ :=
  ∑ y : Fin (N + 1) → S, if workRev E y = w then Prev beta E K y else 0

/-- **Crooks fluctuation theorem.**  For a system driven by the protocol `E` with transition
weights `K` obeying detailed balance at inverse temperature `beta`, the work distribution
`PF` of the forward experiment and the work distribution `PR` of the reverse experiment
satisfy `P_F(W) = e^{β (W - ΔF)} P_R(-W)`, equivalently
`P_F(W) / P_R(-W) = e^{β (W - ΔF)}` whenever the denominator does not vanish. -/
theorem crooks_theorem (beta : ℝ) (hbeta : beta ≠ 0) (E : Fin (N + 1) → S → ℝ)
    (K : Fin N → S → S → ℝ) (hDB : DetailedBalance beta E K) (w : ℝ) :
    PF beta E K w = Real.exp (beta * (w - deltaF beta E)) * PR beta E K (-w) ∧
      (PR beta E K (-w) ≠ 0 →
        PF beta E K w / PR beta E K (-w) = Real.exp (beta * (w - deltaF beta E))) := by
  have key : PF beta E K w = Real.exp (beta * (w - deltaF beta E)) * PR beta E K (-w) := by
    rw [PF, PR, Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.arrowCongr (Fin.revPerm (n := N + 1)) (Equiv.refl S))
      (fun y : Fin (N + 1) → S =>
        Real.exp (beta * (w - deltaF beta E)) * (if workRev E y = -w then Prev beta E K y else 0))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hrev : (Equiv.arrowCongr (Fin.revPerm (n := N + 1)) (Equiv.refl S)) x = revTraj x := by
      funext k
      simp [Equiv.arrowCongr, revTraj]
    rw [hrev, workRev_revTraj]
    by_cases hx : work E x = w
    · rw [if_pos hx, if_pos (by rw [hx])]
      rw [crooks_pathwise beta hbeta E K hDB x, hx]
    · rw [if_neg hx, if_neg (by simpa using hx), mul_zero]
  refine ⟨key, fun h => ?_⟩
  rw [key, mul_div_assoc, div_self h, mul_one]

omit [Nonempty S] in
/-- The hypotheses of `crooks_theorem` are satisfiable: the heat-bath (Glauber) kernels,
which resample the state from the instantaneous Boltzmann distribution, obey detailed
balance. -/
lemma detailedBalance_heatBath (beta : ℝ) (E : Fin (N + 1) → S → ℝ) :
    DetailedBalance beta E
      (fun k _ b => Real.exp (-beta * E k.succ b) / Zpart beta (E k.succ)) := by
  intro k a b
  field_simp

end Main

end Phys

section Sanity

#print axioms Phys.crooks_theorem

end Sanity

