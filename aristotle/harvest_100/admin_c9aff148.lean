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

namespace Frontier

/-! ## Gibbs' inequality (nonnegativity of relative entropy) -/

/-- Gibbs' inequality on a finite index type: the relative entropy (Kullback–Leibler
divergence) of two probability distributions is nonnegative, provided `p` is absolutely
continuous with respect to `q`. -/
theorem sum_mul_log_div_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, 0 < p i → 0 < q i)
    (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have key : ∀ i, p i * Real.log (q i / p i) ≤ q i - p i := by
    intro i
    rcases (hp i).lt_or_eq with h | h
    · have hqi := hac i h
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqi h)
      calc p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
            mul_le_mul_of_nonneg_left hlog h.le
        _ = q i - p i := by field_simp
    · rw [← h]
      simpa using hq i
  have hsum : ∑ i, p i * Real.log (q i / p i) ≤ 0 := by
    calc ∑ i, p i * Real.log (q i / p i) ≤ ∑ i, (q i - p i) :=
          Finset.sum_le_sum fun i _ => key i
      _ = 0 := by rw [Finset.sum_sub_distrib, hsp, hsq, sub_self]
  have heq : ∑ i, p i * Real.log (p i / q i) = -∑ i, p i * Real.log (q i / p i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show p i / q i = (q i / p i)⁻¹ from (inv_div _ _).symm, Real.log_inv]
    ring
  rw [heq]
  linarith

/-! ## Systems, mechanisms and the cut (partitioned) dynamics -/

/-- A finite discrete dynamical system: `V` is the set of elements (nodes), `S` the set of
states of a single element, and `tpm v s t` is the probability that element `v` is in state
`t` at the next time step, given that the whole system is in state `s` now.  Elements update
independently of each other given the current global state (this is the standard
transition-probability-matrix setting used in integrated information theory). -/
structure System (V S : Type*) [Fintype V] [DecidableEq V] [Fintype S] where
  /-- `tpm v s t`: probability that node `v` transitions to state `t` from global state `s`. -/
  tpm : V → (V → S) → S → ℝ
  tpm_nonneg : ∀ v s t, 0 ≤ tpm v s t
  tpm_sum : ∀ v s, ∑ t, tpm v s t = 1

namespace System

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [Nonempty S]

/-- The joint transition probability of the whole system: the probability of the next global
state `s'` given the current global state `s`. -/
noncomputable def prob (M : System V S) (s s' : V → S) : ℝ := ∏ v, M.tpm v s (s' v)

/-- `glue A s u` is the state that agrees with `s` on `A` and with `u` off `A`. -/
def glue (A : Finset V) (s u : V → S) : V → S := fun w => if w ∈ A then s w else u w

/-- The mechanism of node `v` after cutting all connections coming from outside the part `A`:
the inputs from outside `A` are replaced by independent uniform noise (i.e. averaged over). -/
noncomputable def cutTpm (M : System V S) (A : Finset V) (v : V) (s : V → S) (t : S) : ℝ :=
  (∑ u : V → S, M.tpm v (glue A s u) t) / (Fintype.card (V → S) : ℝ)

/-- The part of the bipartition `{A, Aᶜ}` containing the node `v`. -/
def part (A : Finset V) (v : V) : Finset V := if v ∈ A then A else Aᶜ

/-- The joint transition probability of the system after applying the cut associated with the
bipartition `{A, Aᶜ}`: every node is driven by its own part only, the inputs coming from the
other part being replaced by noise. -/
noncomputable def cutProb (M : System V S) (A : Finset V) (s s' : V → S) : ℝ :=
  ∏ v, M.cutTpm (part A v) v s (s' v)

/-- The effective information of the bipartition `{A, Aᶜ}` at the state `s`: the relative
entropy between the actual next-state distribution and the one produced by the cut system. -/
noncomputable def EI (M : System V S) (A : Finset V) (s : V → S) : ℝ :=
  ∑ s' : V → S, M.prob s s' * Real.log (M.prob s s' / M.cutProb A s s')

/-- The set of bipartitions of the system: nonempty proper subsets `A` of the set of nodes,
each one standing for the bipartition `{A, Aᶜ}`. -/
def Bipartitions (V : Type*) [Fintype V] [DecidableEq V] : Set (Finset V) :=
  {A | A.Nonempty ∧ A ≠ Finset.univ}

/-- **Integrated information** `Φ` of the system at a state `s`: the minimum of the effective
information over all bipartitions of the system. -/
noncomputable def Phi (M : System V S) (s : V → S) : ℝ :=
  sInf {x : ℝ | ∃ A ∈ Bipartitions V, x = M.EI A s}

/-- The mechanisms of the nodes of `A` depend only on the current state of `A`. -/
def IndepOn (M : System V S) (A : Finset V) : Prop :=
  ∀ v ∈ A, ∀ s s' : V → S, (∀ w ∈ A, s w = s' w) → M.tpm v s = M.tpm v s'

/-- The system splits into the two non-interacting subsystems `A` and `Aᶜ`. -/
def Disconnected (M : System V S) (A : Finset V) : Prop :=
  M.IndepOn A ∧ M.IndepOn Aᶜ

/-! ## Basic facts -/

omit [Nonempty S] in
theorem prob_nonneg (M : System V S) (s s' : V → S) : 0 ≤ M.prob s s' :=
  Finset.prod_nonneg fun v _ => M.tpm_nonneg v s (s' v)

omit [Nonempty S] in
theorem sum_prob (M : System V S) (s : V → S) : ∑ s' : V → S, M.prob s s' = 1 := by
  have h : ∑ s' : V → S, (∏ v, M.tpm v s (s' v)) = ∏ v, ∑ t, M.tpm v s t := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [prob, h, M.tpm_sum]

omit [Nonempty S] in
theorem cutTpm_nonneg (M : System V S) (A : Finset V) (v : V) (s : V → S) (t : S) :
    0 ≤ M.cutTpm A v s t :=
  div_nonneg (Finset.sum_nonneg fun _ _ => M.tpm_nonneg _ _ _) (Nat.cast_nonneg _)

theorem card_pi_pos : (0 : ℝ) < (Fintype.card (V → S) : ℝ) := by
  exact_mod_cast Fintype.card_pos (α := V → S)

theorem sum_cutTpm (M : System V S) (A : Finset V) (v : V) (s : V → S) :
    ∑ t, M.cutTpm A v s t = 1 := by
  unfold cutTpm
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [M.tpm_sum]
  simp [Finset.card_univ]

omit [Nonempty S] in
theorem cutProb_nonneg (M : System V S) (A : Finset V) (s s' : V → S) :
    0 ≤ M.cutProb A s s' :=
  Finset.prod_nonneg fun _ _ => M.cutTpm_nonneg _ _ _ _

theorem sum_cutProb (M : System V S) (A : Finset V) (s : V → S) :
    ∑ s' : V → S, M.cutProb A s s' = 1 := by
  have h : ∑ s' : V → S, (∏ v, M.cutTpm (part A v) v s (s' v))
      = ∏ v, ∑ t, M.cutTpm (part A v) v s t := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [cutProb, h, M.sum_cutTpm]

/-- Absolute continuity: the cut dynamics can do everything the actual dynamics can. -/
theorem cutProb_pos_of_prob_pos (M : System V S) (A : Finset V) (s s' : V → S)
    (h : 0 < M.prob s s') : 0 < M.cutProb A s s' := by
  have hfac : ∀ v : V, 0 < M.tpm v s (s' v) := by
    intro v
    rcases (M.tpm_nonneg v s (s' v)).lt_or_eq with hv | hv
    · exact hv
    · exact absurd (Finset.prod_eq_zero (Finset.mem_univ v) hv.symm) h.ne'
  refine Finset.prod_pos fun v _ => ?_
  have hglue : glue (part A v) s s = s := by
    funext w; simp [glue]
  have hle : M.tpm v s (s' v) ≤ ∑ u : V → S, M.tpm v (glue (part A v) s u) (s' v) := by
    have := Finset.single_le_sum
      (f := fun u : V → S => M.tpm v (glue (part A v) s u) (s' v))
      (fun u _ => M.tpm_nonneg _ _ _) (Finset.mem_univ s)
    simpa only [hglue] using this
  exact div_pos (lt_of_lt_of_le (hfac v) hle) (card_pi_pos (V := V) (S := S))

/-- Effective information is always nonnegative. -/
theorem EI_nonneg (M : System V S) (A : Finset V) (s : V → S) : 0 ≤ M.EI A s :=
  Frontier.sum_mul_log_div_nonneg _ _ (fun s' => M.prob_nonneg s s')
    (fun s' => M.cutProb_nonneg A s s') (fun s' h => M.cutProb_pos_of_prob_pos A s s' h)
    (M.sum_prob s) (M.sum_cutProb A s)

/-- For a disconnected system, the cut along the splitting bipartition changes nothing. -/
theorem cutProb_eq_prob_of_disconnected (M : System V S) {A : Finset V}
    (hA : M.Disconnected A) (s s' : V → S) : M.cutProb A s s' = M.prob s s' := by
  have hN : (Fintype.card (V → S) : ℝ) ≠ 0 := (card_pi_pos (V := V) (S := S)).ne'
  refine Finset.prod_congr rfl fun v _ => ?_
  have hconst : ∀ u : V → S, M.tpm v (glue (part A v) s u) = M.tpm v s := by
    intro u
    by_cases hv : v ∈ A
    · refine hA.1 v hv _ _ fun w hw => ?_
      simp [glue, part, hv, hw]
    · have hv' : v ∈ Aᶜ := Finset.mem_compl.2 hv
      refine hA.2 v hv' _ _ fun w hw => ?_
      simp [glue, part, hv, hw]
  unfold cutTpm
  simp only [fun u => congrFun (hconst u) (s' v)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- For a disconnected system, the effective information of the splitting bipartition is `0`. -/
theorem EI_eq_zero_of_disconnected (M : System V S) {A : Finset V}
    (hA : M.Disconnected A) (s : V → S) : M.EI A s = 0 := by
  refine Finset.sum_eq_zero fun s' _ => ?_
  rw [M.cutProb_eq_prob_of_disconnected hA s s']
  rcases eq_or_ne (M.prob s s') 0 with h | h
  · simp [h]
  · simp [div_self h]

end System

/-- **Integrated information vanishes for a disconnected system.**

`Φ`, defined as the minimum over all bipartitions `{A, Aᶜ}` of the system of the effective
information `EI` (the relative entropy between the actual next-state distribution and the
distribution obtained after cutting the connections between the two parts), is equal to `0`
whenever the system splits into two non-interacting subsystems. -/
theorem iit_phi_partition {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [Nonempty S]
    (M : System V S) {A : Finset V} (hA : A ∈ System.Bipartitions V)
    (hdis : M.Disconnected A) (s : V → S) :
    M.Phi s = 0 := by
  have hlb : ∀ x ∈ {x : ℝ | ∃ A ∈ System.Bipartitions V, x = M.EI A s}, 0 ≤ x := by
    rintro x ⟨B, -, rfl⟩
    exact M.EI_nonneg B s
  have hmem : (0 : ℝ) ∈ {x : ℝ | ∃ A ∈ System.Bipartitions V, x = M.EI A s} :=
    ⟨A, hA, (M.EI_eq_zero_of_disconnected hdis s).symm⟩
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun x hx => hlb x hx⟩ hmem
  · exact le_csInf ⟨0, hmem⟩ hlb

/-- The hypotheses of `Frontier.iit_phi_partition` are satisfiable: there is a genuine
two-element system together with a bipartition along which it is disconnected. -/
theorem exists_disconnected_system :
    ∃ (M : System Bool Bool) (A : Finset Bool),
      A ∈ System.Bipartitions Bool ∧ M.Disconnected A := by
  refine ⟨⟨fun _ _ _ => 1 / 2, by norm_num, by intro _ _; simp⟩, {true}, ⟨⟨true, by simp⟩, ?_⟩,
    ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩
  intro h
  have : (false : Bool) ∈ ({true} : Finset Bool) := h ▸ Finset.mem_univ false
  simp at this

end Frontier

