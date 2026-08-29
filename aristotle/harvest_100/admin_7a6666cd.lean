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
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/
def st {X : Type*} {N : ℕ} (γ : Fin (N + 1) → X) (n : ℕ) : X :=
  γ ⟨min n N, by omega⟩

/-- Partition function of the energy `E t` at inverse temperature `β`. -/
noncomputable def Zpf (β : ℝ) (E : ℕ → X → ℝ) (t : ℕ) : ℝ :=
  ∑ x : X, Real.exp (-β * E t x)

/-- Probability of the forward trajectory `γ`: start in equilibrium w.r.t. `E 0`, then at each
step `t < N` the protocol changes `E t → E (t+1)` at fixed state (this is where work is done)
and afterwards the system relaxes with the transition kernel `p t`. -/
noncomputable def Pfwd (β : ℝ) (E : ℕ → X → ℝ) (p : ℕ → X → X → ℝ) (N : ℕ)
    (γ : Fin (N + 1) → X) : ℝ :=
  Real.exp (-β * E 0 (st γ 0)) / Zpf β E 0 * ∏ t ∈ range N, p t (st γ t) (st γ (t + 1))

/-- Work done on the system along the forward trajectory `γ`. -/
def Wfwd (E : ℕ → X → ℝ) (N : ℕ) (γ : Fin (N + 1) → X) : ℝ :=
  ∑ t ∈ range N, (E (t + 1) (st γ t) - E t (st γ t))

/-- Energies of the time-reversed protocol. -/
def Erev (E : ℕ → X → ℝ) (N : ℕ) (s : ℕ) (x : X) : ℝ := E (N - s) x

/-- Transition kernels of the time-reversed protocol. -/
def prev (p : ℕ → X → X → ℝ) (N : ℕ) (s : ℕ) (x y : X) : ℝ := p (N - 1 - s) x y

/-- Probability of the trajectory `δ` in the reverse process: start in equilibrium w.r.t. `E N`,
then at each step `s < N` the system first relaxes with the kernel `prev p N s` and afterwards
the protocol changes `Erev E N s → Erev E N (s+1)` at fixed state. -/
noncomputable def Prev (β : ℝ) (E : ℕ → X → ℝ) (p : ℕ → X → X → ℝ) (N : ℕ)
    (δ : Fin (N + 1) → X) : ℝ :=
  Real.exp (-β * Erev E N 0 (st δ 0)) / Zpf β (Erev E N) 0 *
    ∏ s ∈ range N, prev p N s (st δ s) (st δ (s + 1))

/-- Work done on the system along the trajectory `δ` of the reverse process. -/
def Wrev (E : ℕ → X → ℝ) (N : ℕ) (δ : Fin (N + 1) → X) : ℝ :=
  ∑ s ∈ range N, (Erev E N (s + 1) (st δ (s + 1)) - Erev E N s (st δ (s + 1)))

/-- Time reversal of a trajectory. -/
def revPath {X : Type*} {N : ℕ} (γ : Fin (N + 1) → X) : Fin (N + 1) → X := fun i => γ i.rev

/-- Free-energy difference between the final and the initial equilibrium states. -/
noncomputable def deltaF (β : ℝ) (E : ℕ → X → ℝ) (N : ℕ) : ℝ :=
  -Real.log (Zpf β E N / Zpf β E 0) / β

/-- Detailed balance: after the protocol step `E t → E (t+1)`, the relaxation kernel `p t`
is in detailed balance with respect to the energy `E (t+1)`. -/
def DetailedBalance (β : ℝ) (E : ℕ → X → ℝ) (p : ℕ → X → X → ℝ) (N : ℕ) : Prop :=
  ∀ t < N, ∀ x y : X,
    p t x y * Real.exp (-β * E (t + 1) x) = p t y x * Real.exp (-β * E (t + 1) y)

section

variable {β : ℝ} {E : ℕ → X → ℝ} {p : ℕ → X → X → ℝ} {N : ℕ}

omit [Fintype X] in
lemma st_revPath (γ : Fin (N + 1) → X) (n : ℕ) : st (revPath γ) n = st γ (N - n) := by
  simp only [st, revPath, Fin.rev]
  congr 1
  ext
  simp
  omega

omit [Fintype X] in
lemma revPath_revPath (γ : Fin (N + 1) → X) : revPath (revPath γ) = γ := by
  funext i
  simp [revPath]

omit [Fintype X] in
/-- The work along the reversed trajectory in the reverse process is minus the forward work. -/
lemma Wrev_revPath (γ : Fin (N + 1) → X) : Wrev E N (revPath γ) = -Wfwd E N γ := by
  simp only [Wrev, Wfwd, Erev, st_revPath, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have e1 : N - (N - 1 - s + 1) = s := by omega
  have e2 : N - (N - 1 - s) = s + 1 := by omega
  rw [e1, e2]
  ring

lemma Zpf_pos [Nonempty X] (t : ℕ) : 0 < Zpf β E t :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype X] in
/-- Detailed balance, applied along a whole trajectory. -/
lemma prod_detailedBalance (hDB : DetailedBalance β E p N) (γ : Fin (N + 1) → X) :
    (∏ t ∈ range N, p t (st γ t) (st γ (t + 1))) *
        Real.exp (-β * ∑ t ∈ range N, E (t + 1) (st γ t)) =
      (∏ t ∈ range N, p t (st γ (t + 1)) (st γ t)) *
        Real.exp (-β * ∑ t ∈ range N, E (t + 1) (st γ (t + 1))) := by
  rw [Finset.mul_sum, Finset.mul_sum, Real.exp_sum, Real.exp_sum, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t ht => hDB t (Finset.mem_range.mp ht) _ _

/-- The reverse-process probability of the reversed trajectory, written in forward data. -/
lemma Prev_revPath (γ : Fin (N + 1) → X) :
    Prev β E p N (revPath γ) =
      Real.exp (-β * E N (st γ N)) / Zpf β E N *
        ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) := by
  have hprod : (∏ s ∈ range N, prev p N s (st (revPath γ) s) (st (revPath γ) (s + 1))) =
      ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) := by
    simp only [prev, st_revPath]
    rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    have e1 : N - 1 - (N - 1 - t) = t := by omega
    have e2 : N - (N - 1 - t) = t + 1 := by omega
    have e3 : N - (N - 1 - t + 1) = t := by omega
    rw [e1, e2, e3]
  have hZ : Zpf β (Erev E N) 0 = Zpf β E N := by
    simp [Zpf, Erev]
  rw [Prev, hprod, hZ]
  simp [Erev, st_revPath]

omit [Fintype X] in
/-- The core exponential identity behind the Crooks relation. -/
lemma crooks_core (hDB : DetailedBalance β E p N) (γ : Fin (N + 1) → X) :
    Real.exp (-β * E 0 (st γ 0)) * ∏ t ∈ range N, p t (st γ t) (st γ (t + 1)) =
      Real.exp (β * Wfwd E N γ) * Real.exp (-β * E N (st γ N)) *
        ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) := by
  set A := ∏ t ∈ range N, p t (st γ t) (st γ (t + 1)) with hA
  set B := ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) with hB
  set S1 := ∑ t ∈ range N, E (t + 1) (st γ t) with hS1
  set S2 := ∑ t ∈ range N, E (t + 1) (st γ (t + 1)) with hS2
  set S0 := ∑ t ∈ range N, E t (st γ t) with hS0
  have hDBp : A * Real.exp (-β * S1) = B * Real.exp (-β * S2) :=
    prod_detailedBalance hDB γ
  have hAeq : A = B * Real.exp (-β * S2 + β * S1) := by
    have h : A * Real.exp (-β * S1) * Real.exp (β * S1) =
        B * Real.exp (-β * S2) * Real.exp (β * S1) := by rw [hDBp]
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add] at h
    simpa using h
  have htel : E 0 (st γ 0) + S2 = S0 + E N (st γ N) := by
    have h1 : (∑ i ∈ range (N + 1), E i (st γ i))
        = (∑ i ∈ range N, E (i + 1) (st γ (i + 1))) + E 0 (st γ 0) :=
      Finset.sum_range_succ' (fun i => E i (st γ i)) N
    have h2 : (∑ i ∈ range (N + 1), E i (st γ i))
        = (∑ i ∈ range N, E i (st γ i)) + E N (st γ N) :=
      Finset.sum_range_succ (fun i => E i (st γ i)) N
    rw [hS2, hS0]
    linarith
  have hW : Wfwd E N γ = S1 - S0 := by
    simp only [Wfwd, hS1, hS0, Finset.sum_sub_distrib]
  rw [hAeq, hW]
  rw [show Real.exp (-β * E 0 (st γ 0)) * (B * Real.exp (-β * S2 + β * S1)) =
      B * (Real.exp (-β * E 0 (st γ 0)) * Real.exp (-β * S2 + β * S1)) by ring,
    show Real.exp (β * (S1 - S0)) * Real.exp (-β * E N (st γ N)) * B =
      B * (Real.exp (β * (S1 - S0)) * Real.exp (-β * E N (st γ N))) by ring,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  linear_combination (-β) * htel

/-- Microscopic (trajectory-level) Crooks relation. -/
theorem crooks_path [Nonempty X] (hβ : β ≠ 0) (hDB : DetailedBalance β E p N)
    (γ : Fin (N + 1) → X) :
    Pfwd β E p N γ = Real.exp (β * (Wfwd E N γ - deltaF β E N)) * Prev β E p N (revPath γ) := by
  have hZ0 : (0 : ℝ) < Zpf β E 0 := Zpf_pos 0
  have hZN : (0 : ℝ) < Zpf β E N := Zpf_pos N
  have hexp : Real.exp (β * (Wfwd E N γ - deltaF β E N)) =
      Real.exp (β * Wfwd E N γ) * (Zpf β E N / Zpf β E 0) := by
    have hpos : (0 : ℝ) < Zpf β E N / Zpf β E 0 := div_pos hZN hZ0
    have hdF : β * deltaF β E N = -Real.log (Zpf β E N / Zpf β E 0) := by
      rw [deltaF]; field_simp
    rw [show β * (Wfwd E N γ - deltaF β E N) =
        β * Wfwd E N γ + Real.log (Zpf β E N / Zpf β E 0) by
      rw [mul_sub, hdF]; ring]
    rw [Real.exp_add, Real.exp_log hpos]
  rw [hexp, Prev_revPath, Pfwd]
  have hcore := crooks_core hDB γ
  simp only [neg_mul] at hcore ⊢
  field_simp
  linear_combination hcore

/-- **Crooks fluctuation theorem** (coarse-grained form): the probability that the forward
process performs work `w` equals `exp (β (w - ΔF))` times the probability that the reverse
process performs work `-w`. -/
theorem crooks_theorem [Nonempty X] (hβ : β ≠ 0) (hDB : DetailedBalance β E p N) (w : ℝ) :
    ∑ γ ∈ Finset.univ.filter (fun γ : Fin (N + 1) → X => Wfwd E N γ = w), Pfwd β E p N γ =
      Real.exp (β * (w - deltaF β E N)) *
        ∑ δ ∈ Finset.univ.filter (fun δ : Fin (N + 1) → X => Wrev E N δ = -w), Prev β E p N δ := by
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun γ => revPath γ) (fun δ => revPath δ) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
    rw [Wrev_revPath, hγ]
  · intro δ hδ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ ⊢
    have h := Wrev_revPath (E := E) (revPath δ)
    rw [revPath_revPath, hδ] at h
    linarith
  · intro γ _
    exact revPath_revPath γ
  · intro δ _
    exact revPath_revPath δ
  · intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    rw [crooks_path hβ hDB γ, hγ]

/-- Ratio form of the Crooks fluctuation theorem: `P_F(W) / P_R(-W) = exp (β (W - ΔF))`. -/
theorem crooks_theorem_ratio [Nonempty X] (hβ : β ≠ 0) (hDB : DetailedBalance β E p N) (w : ℝ)
    (hne : ∑ δ ∈ Finset.univ.filter (fun δ : Fin (N + 1) → X => Wrev E N δ = -w), Prev β E p N δ ≠ 0) :
    (∑ γ ∈ Finset.univ.filter (fun γ : Fin (N + 1) → X => Wfwd E N γ = w), Pfwd β E p N γ) /
        (∑ δ ∈ Finset.univ.filter (fun δ : Fin (N + 1) → X => Wrev E N δ = -w), Prev β E p N δ) =
      Real.exp (β * (w - deltaF β E N)) := by
  rw [crooks_theorem hβ hDB w, mul_div_assoc, div_self hne, mul_one]

/-- The heat-bath (Gibbs) relaxation kernel for the protocol step `t`. -/
noncomputable def gibbsKernel (β : ℝ) (E : ℕ → X → ℝ) (t : ℕ) (_x y : X) : ℝ :=
  Real.exp (-β * E (t + 1) y) / Zpf β E (t + 1)

/-- The heat-bath kernel is a genuine transition kernel: it is nonnegative and normalized. -/
lemma gibbsKernel_nonneg (t : ℕ) (x y : X) : 0 ≤ gibbsKernel β E t x y := by
  have := Real.exp_pos (-β * E (t + 1) y)
  exact div_nonneg this.le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

lemma gibbsKernel_sum [Nonempty X] (t : ℕ) (x : X) : ∑ y : X, gibbsKernel β E t x y = 1 := by
  simp only [gibbsKernel]
  rw [← Finset.sum_div]
  exact div_self (Zpf_pos (β := β) (E := E) (t + 1)).ne'

/-- The heat-bath kernel satisfies detailed balance, so the hypotheses of the Crooks theorem
are non-vacuous. -/
lemma gibbsKernel_detailedBalance : DetailedBalance β E (gibbsKernel β E) N := by
  intro t _ x y
  simp only [gibbsKernel]
  ring

lemma Pfwd_gibbs_pos [Nonempty X] (γ : Fin (N + 1) → X) :
    0 < Pfwd β E (gibbsKernel β E) N γ := by
  refine mul_pos (div_pos (Real.exp_pos _) (Zpf_pos 0)) (Finset.prod_pos fun t _ => ?_)
  exact div_pos (Real.exp_pos _) (Zpf_pos _)

lemma Prev_gibbs_pos [Nonempty X] (δ : Fin (N + 1) → X) :
    0 < Prev β E (gibbsKernel β E) N δ := by
  refine mul_pos (div_pos (Real.exp_pos _) (Zpf_pos 0)) (Finset.prod_pos fun s _ => ?_)
  exact div_pos (Real.exp_pos _) (Zpf_pos _)

/-- Non-vacuity of the ratio form: for the heat-bath dynamics and any work value that is
actually realized by some trajectory, both work distributions are supported at `±w` and the
Crooks ratio `P_F(w) / P_R(-w) = exp (β (w - ΔF))` holds. -/
theorem crooks_theorem_ratio_gibbs [Nonempty X] (hβ : β ≠ 0) (γ₀ : Fin (N + 1) → X) :
    (∑ γ ∈ Finset.univ.filter (fun γ : Fin (N + 1) → X => Wfwd E N γ = Wfwd E N γ₀),
        Pfwd β E (gibbsKernel β E) N γ) /
      (∑ δ ∈ Finset.univ.filter (fun δ : Fin (N + 1) → X => Wrev E N δ = -Wfwd E N γ₀),
        Prev β E (gibbsKernel β E) N δ) =
      Real.exp (β * (Wfwd E N γ₀ - deltaF β E N)) := by
  refine crooks_theorem_ratio hβ gibbsKernel_detailedBalance _ (ne_of_gt ?_)
  refine Finset.sum_pos (fun δ _ => Prev_gibbs_pos δ) ⟨revPath γ₀, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Wrev_revPath γ₀

end

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

