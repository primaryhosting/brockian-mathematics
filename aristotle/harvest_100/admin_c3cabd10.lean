/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

namespace Frontier

/-!
## Setting

A *system* consists of a finite collection `ι` of binary elements.  A global state of the
system is a function `s : ι → Bool`.  The dynamics is given by a mechanism for each element:
`prob i s b` is the probability that element `i` takes the value `b` at the next time step,
given that the system is currently in state `s`.  Elements update independently given the
current global state, so the transition probability matrix of the whole system is the product
`tpm M s t = ∏ i, prob i s (t i)`.

Integrated information `Φ` is obtained by *cutting* the system along a bipartition
`(A, Aᶜ)`: the influence that each part receives from the other part is replaced by
independent noise (an average over the states of the other part).  The *effective information*
`ei M A` of a bipartition is the (state-averaged) `L¹` distance between the true transition
matrix and the transition matrix of the cut system, and `Φ` is the infimum of `ei M A` over
all bipartitions of the system.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite system of binary elements, each equipped with a stochastic mechanism
`prob i s : Bool → ℝ` giving the distribution of the next value of element `i` when the
system is currently in the global state `s`. -/
structure System (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- `prob i s b` is the probability that element `i` takes the value `b` at the next
  time step, given the current global state `s`. -/
  prob : ι → (ι → Bool) → Bool → ℝ
  prob_nonneg : ∀ (i : ι) (s : ι → Bool) (b : Bool), 0 ≤ prob i s b
  prob_sum : ∀ (i : ι) (s : ι → Bool), prob i s false + prob i s true = 1

/-- `mergeOn A s u` is the state that agrees with `s` on `A` and with `u` off `A`. -/
def mergeOn (A : Finset ι) (s u : ι → Bool) : ι → Bool := fun j => if j ∈ A then s j else u j

/-- The mechanism of element `i` after the elements outside the part `A` have been replaced
by independent uniform noise: the value on `A` is read off from the current state `s`, while
the values outside `A` are averaged out uniformly. -/
noncomputable def cutProb (M : System ι) (A : Finset ι) (i : ι) (s : ι → Bool) (b : Bool) : ℝ :=
  (∑ u : ι → Bool, M.prob i (mergeOn A s u) b) / (Fintype.card (ι → Bool) : ℝ)

/-- The transition probability matrix of the system: elements update independently given the
current global state. -/
noncomputable def tpm (M : System ι) (s t : ι → Bool) : ℝ := ∏ i : ι, M.prob i s (t i)

/-- The transition probability matrix of the system cut along the bipartition `(A, Aᶜ)`:
every element updates using only the current state of its own part, the other part being
replaced by independent uniform noise. -/
noncomputable def cutTpm (M : System ι) (A : Finset ι) (s t : ι → Bool) : ℝ :=
  ∏ i : ι, cutProb M (if i ∈ A then A else Aᶜ) i s (t i)

/-- The effective information of the bipartition `(A, Aᶜ)`: the `L¹` distance between the
true transition matrix and the cut transition matrix, averaged over the current state. -/
noncomputable def ei (M : System ι) (A : Finset ι) : ℝ :=
  (∑ s : ι → Bool, ∑ t : ι → Bool, |tpm M s t - cutTpm M A s t|) / (Fintype.card (ι → Bool) : ℝ)

/-- The bipartitions of the system: proper nonempty subsets `A`, cutting the system into
the two parts `A` and `Aᶜ`. -/
def Bipartitions (ι : Type*) [Fintype ι] [DecidableEq ι] : Set (Finset ι) :=
  {A : Finset ι | A.Nonempty ∧ A ≠ Finset.univ}

/-- Integrated information: the minimal effective information over all bipartitions. -/
noncomputable def Phi (M : System ι) : ℝ := sInf (ei M '' Bipartitions ι)

/-- A system is *disconnected* if its elements split into two nonempty parts `A` and `Aᶜ`
such that the mechanism of every element of a part depends only on the current state of that
same part. -/
def Disconnected (M : System ι) : Prop :=
  ∃ A : Finset ι, A.Nonempty ∧ A ≠ Finset.univ ∧
    (∀ i ∈ A, ∀ s s' : ι → Bool, (∀ j ∈ A, s j = s' j) → M.prob i s = M.prob i s') ∧
    (∀ i ∉ A, ∀ s s' : ι → Bool, (∀ j ∉ A, s j = s' j) → M.prob i s = M.prob i s')

/-! ## Basic facts -/

theorem card_state_pos : 0 < (Fintype.card (ι → Bool)) :=
  Fintype.card_pos

theorem card_state_ne_zero : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
  exact_mod_cast card_state_pos.ne'

theorem ei_nonneg (M : System ι) (A : Finset ι) : 0 ≤ ei M A := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun s _ =>
      Finset.sum_nonneg fun t _ => abs_nonneg _
  · exact Nat.cast_nonneg _

theorem Phi_nonneg (M : System ι) : 0 ≤ Phi M := by
  rcases Set.eq_empty_or_nonempty (ei M '' Bipartitions ι) with h | h
  · simp [Phi, h]
  · exact le_csInf h (by rintro x ⟨A, -, rfl⟩; exact ei_nonneg M A)

/-! ## The key computation: a part that is closed under the dynamics is unaffected by the cut -/

omit [Fintype ι] in
theorem mergeOn_agrees (A : Finset ι) (s u : ι → Bool) {j : ι} (hj : j ∈ A) :
    mergeOn A s u j = s j := by
  simp [mergeOn, hj]

/-- If the mechanism of `i` depends only on the elements of `A`, then cutting away everything
outside `A` does not change it. -/
theorem cutProb_eq_prob_of_indep (M : System ι) (A : Finset ι) (i : ι)
    (hi : ∀ s s' : ι → Bool, (∀ j ∈ A, s j = s' j) → M.prob i s = M.prob i s')
    (s : ι → Bool) (b : Bool) : cutProb M A i s b = M.prob i s b := by
  have hconst : ∀ u : ι → Bool, M.prob i (mergeOn A s u) b = M.prob i s b := by
    intro u
    have := hi (mergeOn A s u) s (fun j hj => mergeOn_agrees A s u hj)
    rw [this]
  rw [cutProb]
  rw [Finset.sum_congr rfl (fun u _ => hconst u)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Cutting a disconnected system along the bipartition witnessing its disconnectedness does
not change the transition matrix. -/
theorem cutTpm_eq_tpm_of_disconnected (M : System ι) (A : Finset ι)
    (hA : ∀ i ∈ A, ∀ s s' : ι → Bool, (∀ j ∈ A, s j = s' j) → M.prob i s = M.prob i s')
    (hAc : ∀ i ∉ A, ∀ s s' : ι → Bool, (∀ j ∉ A, s j = s' j) → M.prob i s = M.prob i s')
    (s t : ι → Bool) : cutTpm M A s t = tpm M s t := by
  rw [cutTpm, tpm]
  refine Finset.prod_congr rfl ?_
  intro i _
  by_cases hi : i ∈ A
  · simp only [hi, if_true]
    exact cutProb_eq_prob_of_indep M A i (hA i hi) s (t i)
  · simp only [hi, if_false]
    refine cutProb_eq_prob_of_indep M Aᶜ i ?_ s (t i)
    intro u v huv
    refine hAc i hi u v ?_
    intro j hj
    exact huv j (by simpa using hj)

/-- The effective information of a cut of a disconnected system into its two disconnected
parts vanishes. -/
theorem ei_eq_zero_of_disconnected (M : System ι) (A : Finset ι)
    (hA : ∀ i ∈ A, ∀ s s' : ι → Bool, (∀ j ∈ A, s j = s' j) → M.prob i s = M.prob i s')
    (hAc : ∀ i ∉ A, ∀ s s' : ι → Bool, (∀ j ∉ A, s j = s' j) → M.prob i s = M.prob i s') :
    ei M A = 0 := by
  have h : ∀ s t : ι → Bool, |tpm M s t - cutTpm M A s t| = 0 := by
    intro s t
    rw [cutTpm_eq_tpm_of_disconnected M A hA hAc s t, sub_self, abs_zero]
  simp [ei, h]

/-! ## Main theorem -/

/-- **Integrated information vanishes for a disconnected system.**
With `Φ` defined as the minimum, over all bipartitions `(A, Aᶜ)` of a finite system of
binary stochastic elements, of the effective information `ei` (the state-averaged `L¹`
distance between the true transition matrix and the transition matrix obtained by cutting
the two parts apart and replacing the influence of each part on the other by noise),
a disconnected system has `Φ = 0`. -/
theorem iit_phi_partition (M : System ι) (h : Disconnected M) : Phi M = 0 := by
  obtain ⟨A, hne, hproper, hA, hAc⟩ := h
  have hmem : ei M A ∈ ei M '' Bipartitions ι := ⟨A, ⟨hne, hproper⟩, rfl⟩
  have hzero : ei M A = 0 := ei_eq_zero_of_disconnected M A hA hAc
  refine le_antisymm ?_ (Phi_nonneg M)
  have hbdd : BddBelow (ei M '' Bipartitions ι) :=
    ⟨0, by rintro x ⟨B, -, rfl⟩; exact ei_nonneg M B⟩
  have := csInf_le hbdd hmem
  rwa [hzero] at this

/-! ## Non-vacuity of the statement -/

/-- Disconnected systems exist: the two-element system in which both elements flip an
independent fair coin. -/
theorem exists_disconnected_system : ∃ M : System Bool, Disconnected M := by
  refine ⟨⟨fun _ _ _ => 1 / 2, by intros; norm_num, by intros; norm_num⟩, {true},
    ⟨true, by simp⟩, by decide, ?_, ?_⟩
  · intro i _ s s' _; rfl
  · intro i _ s s' _; rfl

/-- The two-element system in which each element copies the current value of the other one. -/
noncomputable def copySystem : System Bool where
  prob := fun i s b => if b = s (!i) then 1 else 0
  prob_nonneg := by intro i s b; split <;> norm_num
  prob_sum := by intro i s; cases s (!i) <;> norm_num

theorem boolfun_univ : (Finset.univ : Finset (Bool → Bool)) =
    {(fun _ => false), (fun b => bif b then true else false),
      (fun b => bif b then false else true), (fun _ => true)} := by decide

theorem sum_boolfun (f : (Bool → Bool) → ℝ) :
    ∑ u : Bool → Bool, f u = f (fun _ => false) + f (fun b => bif b then true else false)
      + f (fun b => bif b then false else true) + f (fun _ => true) := by
  rw [boolfun_univ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem copy_tpm_false : tpm copySystem (fun _ => false) (fun _ => false) = 1 := by
  simp [tpm, copySystem]

theorem copy_cutTpm_false :
    cutTpm copySystem {true} (fun _ => false) (fun _ => false) = 1 / 4 := by
  have hcard : (Fintype.card (Bool → Bool) : ℝ) = 4 := by norm_num
  simp only [cutTpm, Fintype.prod_bool, cutProb, copySystem, mergeOn, hcard]
  rw [sum_boolfun, sum_boolfun]
  norm_num

/-- The effective information of a bipartition is not identically zero: for the two-element
system in which each element copies the other, cutting the two elements apart changes the
dynamics. -/
theorem ei_copySystem_pos : 0 < ei copySystem {true} := by
  have hcard : (0 : ℝ) < (Fintype.card (Bool → Bool) : ℝ) := by norm_num
  refine div_pos ?_ hcard
  refine Finset.sum_pos' (fun s _ => Finset.sum_nonneg fun t _ => abs_nonneg _) ?_
  refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
  refine Finset.sum_pos' (fun t _ => abs_nonneg _) ⟨fun _ => false, Finset.mem_univ _, ?_⟩
  rw [copy_tpm_false, copy_cutTpm_false]
  norm_num

end Frontier

