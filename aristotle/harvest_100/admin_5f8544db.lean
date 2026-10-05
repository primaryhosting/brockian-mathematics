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

/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module doc-comment, so the header
-- above is repeated as the module documentation just after the import.)
import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Shannon entropy of a finite distribution (in nats) -/

/-- Shannon entropy (in nats) of a distribution `p` on a finite type,
using the standard convention `0 * log 0 = 0`. -/
noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (p x)

/-- The Gibbs (canonical) distribution of a reservoir with energy levels `E`
at inverse temperature `β`. -/
noncomputable def gibbs {R : Type*} [Fintype R] (β : ℝ) (E : R → ℝ) (r : R) : ℝ :=
  Real.exp (-(β * E r)) / ∑ r', Real.exp (-(β * E r'))

lemma sum_mul_log_eq_neg_entropy {α : Type*} [Fintype α] (p : α → ℝ) :
    ∑ x, p x * Real.log (p x) = -entropy p := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- Entropy is invariant under a bijective relabelling of the state space.  In particular an
invertible (Hamiltonian/Liouville) evolution of a closed system preserves its Shannon entropy,
which is the situation covered by the entropy hypothesis of `landauer_bound`. -/
lemma entropy_comp_equiv {α : Type*} [Fintype α] (e : α ≃ α) (p : α → ℝ) :
    entropy (p ∘ e) = entropy p :=
  Equiv.sum_comp e (fun y => Real.negMulLog (p y))

section Gibbs

variable {R : Type*} [Fintype R] [Nonempty R] (β : ℝ) (E : R → ℝ)

/-- The partition function is positive. -/
lemma partition_pos : 0 < ∑ r, Real.exp (-(β * E r)) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) (by simp [Finset.univ_nonempty])

lemma gibbs_pos (r : R) : 0 < gibbs β E r :=
  div_pos (Real.exp_pos _) (partition_pos β E)

/-- The Gibbs distribution is normalised. -/
lemma sum_gibbs : ∑ r, gibbs β E r = 1 := by
  simp only [gibbs, ← Finset.sum_div]
  exact div_self (partition_pos β E).ne'

lemma log_gibbs (r : R) :
    Real.log (gibbs β E r) = -(β * E r) - Real.log (∑ r', Real.exp (-(β * E r'))) := by
  simp only [gibbs]
  rw [Real.log_div (Real.exp_ne_zero _) (partition_pos β E).ne', Real.log_exp]

end Gibbs

/-! ## Gibbs' inequality (nonnegativity of relative entropy) -/

/-- **Gibbs' inequality**: for a probability distribution `q` and a subprobability
distribution `m` on a finite type, with `q` absolutely continuous with respect to `m`,
the cross entropy dominates the entropy. -/
theorem sum_mul_log_le {α : Type*} [Fintype α] (q m : α → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (hm0 : ∀ x, 0 ≤ m x)
    (hq1 : ∑ x, q x = 1) (hm1 : ∑ x, m x ≤ 1)
    (hac : ∀ x, q x ≠ 0 → m x ≠ 0) :
    ∑ x, q x * Real.log (m x) ≤ ∑ x, q x * Real.log (q x) := by
  have key : ∀ x : α, q x * Real.log (m x) - q x * Real.log (q x) ≤ m x - q x := by
    intro x
    rcases eq_or_lt_of_le (hq0 x) with h | h
    · simp [← h, hm0 x]
    · have hmx : 0 < m x := lt_of_le_of_ne (hm0 x) (fun hh => hac x h.ne' hh.symm)
      have hlog : Real.log (m x / q x) ≤ m x / q x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hmx h)
      rw [Real.log_div hmx.ne' h.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog h.le
      calc q x * Real.log (m x) - q x * Real.log (q x)
          = q x * (Real.log (m x) - Real.log (q x)) := by ring
        _ ≤ q x * (m x / q x - 1) := hmul
        _ = m x - q x := by field_simp
  have hsum : ∑ x, (q x * Real.log (m x) - q x * Real.log (q x)) ≤ ∑ x, (m x - q x) :=
    Finset.sum_le_sum (fun x _ => key x)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq1] at hsum
  linarith

/-! ## Entropy computations -/

/-- A memory holding exactly one unpredictable bit has entropy `log 2`. -/
lemma entropy_two_point {S : Type*} [Fintype S] [DecidableEq S] {s₀ s₁ : S} (hs : s₀ ≠ s₁)
    (p : S → ℝ) (hp : ∀ s, p s = if s = s₀ ∨ s = s₁ then 1 / 2 else 0) :
    entropy p = Real.log 2 := by
  have h : ∀ s : S, Real.negMulLog (p s)
      = if s ∈ ({s₀, s₁} : Finset S) then Real.negMulLog (1 / 2) else 0 := by
    intro s
    rw [hp s]
    by_cases hmem : s = s₀ ∨ s = s₁ <;> simp [hmem, Finset.mem_insert]
  rw [entropy, Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.card_pair hs, Real.negMulLog,
    show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
  ring

/-- A two-state distribution `(1/2, 1/2)` is normalised. -/
lemma sum_two_point {S : Type*} [Fintype S] [DecidableEq S] {s₀ s₁ : S} (hs : s₀ ≠ s₁)
    (p : S → ℝ) (hp : ∀ s, p s = if s = s₀ ∨ s = s₁ then 1 / 2 else 0) :
    ∑ s, p s = 1 := by
  have h : ∀ s : S, p s = if s ∈ ({s₀, s₁} : Finset S) then (1 : ℝ) / 2 else 0 := by
    intro s
    rw [hp s]
    by_cases hmem : s = s₀ ∨ s = s₁ <;> simp [hmem, Finset.mem_insert]
  rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.card_pair hs]
  norm_num

/-- A memory in a definite state has zero entropy. -/
lemma entropy_eq_zero_of_deterministic {S : Type*} [Fintype S] [DecidableEq S] (p : S → ℝ)
    (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {t : S} (ht : p t = 1) :
    entropy p = 0 := by
  have hzero : ∀ s, s ≠ t → p s = 0 := by
    have hsplit : ∑ s ∈ Finset.univ.erase t, p s = 0 := by
      have hadd := Finset.add_sum_erase Finset.univ p (Finset.mem_univ t)
      rw [ht] at hadd
      linarith [hp1, hadd]
    intro s hst
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp0 x)).1 hsplit s
      (Finset.mem_erase.2 ⟨hst, Finset.mem_univ s⟩)
  rw [entropy]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  by_cases hst : s = t
  · rw [hst, ht]; simp [Real.negMulLog]
  · rw [hzero s hst]; simp

/-! ## The general Landauer bound -/

/-- **Landauer's bound.**  A memory `S` with state distribution `pS` is coupled to a reservoir
`R` in the Gibbs state at inverse temperature `β`, so that the initial joint distribution is the
product `pS ⊗ gibbs β E`.  The composite system evolves to a joint distribution `q` whose Shannon
entropy is at least that of the initial state (the second law for a closed system; an invertible
Hamiltonian evolution even preserves the entropy, cf. `entropy_comp_equiv`, and any bistochastic
evolution can only increase it).  Writing `qS` for the final memory marginal, the entropy lost by
the memory is then at most `β` times the heat delivered to the reservoir. -/
theorem landauer_bound {S R : Type*} [Fintype S] [Fintype R] [Nonempty R]
    (β : ℝ) (E : R → ℝ)
    (pS : S → ℝ) (hpS0 : ∀ s, 0 ≤ pS s) (hpS1 : ∑ s, pS s = 1)
    (q : S × R → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hent : entropy (fun y : S × R => pS y.1 * gibbs β E y.2) ≤ entropy q)
    (qS : S → ℝ) (hqS : ∀ s, qS s = ∑ r, q (s, r)) :
    entropy pS - entropy qS ≤
      β * ((∑ x, q x * E x.2) - ∑ r, gibbs β E r * E r) := by
  set Z := ∑ r, Real.exp (-(β * E r)) with hZdef
  set ρ := gibbs β E with hρdef
  have hρpos : ∀ r, 0 < ρ r := gibbs_pos β E
  have hρsum : ∑ r, ρ r = 1 := sum_gibbs β E
  have hlogρ : ∀ r, Real.log (ρ r) = -(β * E r) - Real.log Z := log_gibbs β E
  have hqS0 : ∀ s, 0 ≤ qS s := fun s => by
    rw [hqS]; exact Finset.sum_nonneg (fun _ _ => hq0 _)
  have hqSsum : ∑ s, qS s = 1 := by
    rw [← hq1, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun s _ => hqS s)
  have hle : ∀ x : S × R, q x ≤ qS x.1 := by
    rintro ⟨s, r⟩
    rw [hqS]
    exact Finset.single_le_sum (f := fun r => q (s, r)) (fun _ _ => hq0 _) (Finset.mem_univ r)
  -- mean reservoir energies, before and after
  set Qi := ∑ r, ρ r * E r with hQi
  set Qf := ∑ x : S × R, q x * E x.2 with hQf
  -- entropy of the initial Gibbs state of the reservoir
  have hρent : ∑ r, ρ r * Real.log (ρ r) = -(β * Qi) - Real.log Z := by
    have hterm : ∀ r, ρ r * Real.log (ρ r) = -(β * (ρ r * E r)) - ρ r * Real.log Z := by
      intro r; rw [hlogρ r]; ring
    rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_sub_distrib, ← Finset.sum_mul,
      hρsum, one_mul, hQi]
    simp [Finset.sum_neg_distrib, ← Finset.mul_sum]
  -- the "reservoir" part of the final cross entropy
  have hqρ : ∑ x : S × R, q x * Real.log (ρ x.2) = -(β * Qf) - Real.log Z := by
    have hterm : ∀ x : S × R, q x * Real.log (ρ x.2)
        = -(β * (q x * E x.2)) - q x * Real.log Z := by
      intro x; rw [hlogρ x.2]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.sum_mul,
      hq1, one_mul, hQf]
    simp [Finset.sum_neg_distrib, ← Finset.mul_sum]
  -- the initial joint entropy: entropy is additive over the product state
  have hprod : ∑ y : S × R, (pS y.1 * ρ y.2) * Real.log (pS y.1 * ρ y.2)
      = -entropy pS + (-(β * Qi) - Real.log Z) := by
    have expand : ∀ s r, (pS s * ρ r) * Real.log (pS s * ρ r)
        = ρ r * (pS s * Real.log (pS s)) + pS s * (ρ r * Real.log (ρ r)) := by
      intro s r
      rcases eq_or_lt_of_le (hpS0 s) with h | h
      · simp [← h]
      · rw [Real.log_mul h.ne' (hρpos r).ne']; ring
    have inner : ∀ s : S, ∑ r, (pS s * ρ r) * Real.log (pS s * ρ r)
        = pS s * Real.log (pS s) + pS s * ∑ r, ρ r * Real.log (ρ r) := by
      intro s
      rw [Finset.sum_congr rfl (fun r _ => expand s r), Finset.sum_add_distrib,
        ← Finset.sum_mul, hρsum, one_mul, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun s _ => inner s),
      Finset.sum_add_distrib, ← Finset.sum_mul, hpS1, one_mul, sum_mul_log_eq_neg_entropy, hρent]
  -- the second law: the final joint entropy is at least the initial one
  have hA : ∑ x, q x * Real.log (q x) ≤ -entropy pS + (-(β * Qi) - Real.log Z) := by
    rw [sum_mul_log_eq_neg_entropy, ← hprod, sum_mul_log_eq_neg_entropy]
    exact neg_le_neg hent
  -- the cross entropy of the final state against the product reference state
  have hB : ∑ x : S × R, q x * Real.log (qS x.1 * ρ x.2)
      = -entropy qS + (-(β * Qf) - Real.log Z) := by
    have split : ∀ x : S × R, q x * Real.log (qS x.1 * ρ x.2)
        = q x * Real.log (qS x.1) + q x * Real.log (ρ x.2) := by
      intro x
      rcases eq_or_lt_of_le (le_trans (hq0 x) (hle x)) with h | h
      · have hqx : q x = 0 := le_antisymm (h ▸ hle x) (hq0 x)
        simp [hqx]
      · rw [Real.log_mul h.ne' (hρpos x.2).ne']; ring
    have hmarg : ∑ x : S × R, q x * Real.log (qS x.1) = ∑ s, qS s * Real.log (qS s) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      show ∑ r, q (s, r) * Real.log (qS s) = qS s * Real.log (qS s)
      rw [← Finset.sum_mul, ← hqS]
    rw [Finset.sum_congr rfl (fun x _ => split x), Finset.sum_add_distrib, hmarg, hqρ,
      sum_mul_log_eq_neg_entropy]
  -- Gibbs' inequality applied to the final joint state and the product reference state
  have hgibbs : ∑ x : S × R, q x * Real.log (qS x.1 * ρ x.2) ≤ ∑ x, q x * Real.log (q x) := by
    refine sum_mul_log_le q (fun x => qS x.1 * ρ x.2) hq0
      (fun x => mul_nonneg (hqS0 _) (hρpos _).le) hq1 (le_of_eq ?_) ?_
    · rw [Fintype.sum_prod_type]
      simp [← Finset.mul_sum, hρsum, hqSsum]
    · intro x hx
      have hpos : 0 < qS x.1 := lt_of_lt_of_le (lt_of_le_of_ne (hq0 x) (Ne.symm hx)) (hle x)
      exact (mul_pos hpos (hρpos x.2)).ne'
  rw [hB] at hgibbs
  rw [mul_sub]
  linarith

/-! ## Landauer's principle -/

/-- **Landauer's principle.**  Erasing one bit of information dissipates at least
`k T log 2` of heat.

A one-bit memory `S` is initially uniformly distributed over two distinguishable states
`s₀ ≠ s₁`, and is coupled to a heat reservoir `R` at temperature `T`, initially in the Gibbs
state at inverse temperature `1 / (k T)`; the initial joint distribution is therefore the
product of the two.  The composite system, being closed, evolves to a joint distribution `q`
whose Shannon entropy is at least the initial joint entropy (invertible Hamiltonian dynamics
preserves it, cf. `entropy_comp_equiv`; any bistochastic dynamics can only increase it), and
after the evolution the memory is with certainty in the single state `t`: the bit has been
erased.  Then the heat `Q` transferred to the reservoir, i.e. the increase of its mean energy,
satisfies `k T log 2 ≤ Q`. -/
theorem landauer_principle {S R : Type*} [Fintype S] [Fintype R] [Nonempty R] [DecidableEq S]
    (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (E : R → ℝ)
    -- the memory starts uniformly distributed over the two states `s₀ ≠ s₁`
    (s₀ s₁ : S) (hs : s₀ ≠ s₁)
    (pS : S → ℝ) (hpS : ∀ s, pS s = if s = s₀ ∨ s = s₁ then 1 / 2 else 0)
    -- `q` is the final joint distribution of memory and reservoir
    (q : S × R → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    -- the second law: the closed composite system does not lose entropy
    (hent : entropy (fun y : S × R => pS y.1 * gibbs (1 / (k * T)) E y.2) ≤ entropy q)
    (qS : S → ℝ) (hqS : ∀ s, qS s = ∑ r, q (s, r))
    -- the bit has been erased: the memory ends up in the definite state `t`
    (t : S) (herase : qS t = 1)
    -- `Q` is the heat dissipated into the reservoir
    (Q : ℝ) (hQ : Q = (∑ x, q x * E x.2) - ∑ r, gibbs (1 / (k * T)) E r * E r) :
    k * T * Real.log 2 ≤ Q := by
  have hkT : 0 < k * T := mul_pos hk hT
  set β := 1 / (k * T) with hβ
  have hpS0 : ∀ s, 0 ≤ pS s := by
    intro s; rw [hpS s]; split <;> norm_num
  have hpS1 : ∑ s, pS s = 1 := sum_two_point hs pS hpS
  -- the initial memory entropy is `log 2`, the final one is `0`
  have hHp : entropy pS = Real.log 2 := entropy_two_point hs pS hpS
  have hqS0 : ∀ s, 0 ≤ qS s := fun s => by
    rw [hqS]; exact Finset.sum_nonneg (fun _ _ => hq0 _)
  have hqSsum : ∑ s, qS s = 1 := by
    rw [← hq1, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun s _ => hqS s)
  have hHq : entropy qS = 0 := entropy_eq_zero_of_deterministic qS hqS0 hqSsum herase
  have hbound := landauer_bound β E pS hpS0 hpS1 q hq0 hq1 hent qS hqS
  rw [hHp, hHq, ← hQ, sub_zero] at hbound
  -- `log 2 ≤ Q / (k T)`, hence `k T log 2 ≤ Q`
  rw [hβ, one_div, inv_mul_eq_div, le_div_iff₀ hkT] at hbound
  linarith [hbound]

/-! ## The hypotheses of Landauer's principle are consistent

We exhibit an explicit erasure process satisfying every hypothesis of `landauer_principle`,
which shows that the statement above is not vacuous.  We take `k = T = 1`, a one-bit memory
`Bool` and a four-state reservoir whose Gibbs state is `(9/10, 1/30, 1/30, 1/30)`; the final
joint state is uniform on `{true} × Fin 4`, so the bit is erased, and the joint entropy has
indeed increased (from `log 2 + H(9/10, 1/30, 1/30, 1/30) ≈ 1.13` to `log 4 ≈ 1.39`). -/

/-- Energy levels of the four-state reservoir used in the explicit example. -/
noncomputable def exampleEnergy : Fin 4 → ℝ := ![0, Real.log 27, Real.log 27, Real.log 27]

lemma exp_neg_log27 : Real.exp (-Real.log 27) = 1 / 27 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

lemma example_partition : ∑ r : Fin 4, Real.exp (-(1 * exampleEnergy r)) = 10 / 9 := by
  simp [Fin.sum_univ_four, exampleEnergy, exp_neg_log27]; norm_num

lemma example_gibbs (r : Fin 4) :
    gibbs 1 exampleEnergy r = if r = 0 then 9 / 10 else 1 / 30 := by
  fin_cases r <;>
    (simp only [gibbs, example_partition]; simp [exampleEnergy, exp_neg_log27] <;> norm_num)

/-- **Non-vacuity of `landauer_principle`.**  There is an explicit one-bit erasure process
(with `k = T = 1`) satisfying all the hypotheses of `landauer_principle`; its dissipated heat
is `13/20 * log 27 ≈ 2.14`, which indeed exceeds `k T log 2 ≈ 0.69`. -/
theorem landauer_erasure_example :
    ∃ (E : Fin 4 → ℝ) (pS : Bool → ℝ) (q : Bool × Fin 4 → ℝ) (qS : Bool → ℝ) (Q : ℝ),
      (∀ s, pS s = if s = false ∨ s = true then 1 / 2 else 0) ∧
      (∀ x, 0 ≤ q x) ∧
      (∑ x, q x = 1) ∧
      entropy (fun y : Bool × Fin 4 => pS y.1 * gibbs (1 / ((1 : ℝ) * 1)) E y.2) ≤ entropy q ∧
      (∀ s, qS s = ∑ r, q (s, r)) ∧
      qS true = 1 ∧
      Q = (∑ x, q x * E x.2) - ∑ r, gibbs (1 / ((1 : ℝ) * 1)) E r * E r ∧
      (1 : ℝ) * 1 * Real.log 2 ≤ Q := by
  have hbeta : (1 : ℝ) / ((1 : ℝ) * 1) = 1 := by norm_num
  set pS : Bool → ℝ := fun _ => 1 / 2 with hpSdef
  set q : Bool × Fin 4 → ℝ := fun x => if x.1 = true then 1 / 4 else 0 with hqdef
  set qS : Bool → ℝ := fun s => if s = true then 1 else 0 with hqSdef
  have hpS : ∀ s : Bool, pS s = if s = false ∨ s = true then (1 : ℝ) / 2 else 0 := by
    intro s; cases s <;> simp [hpSdef]
  have hq0 : ∀ x : Bool × Fin 4, 0 ≤ q x := by intro x; simp only [hqdef]; positivity
  have hq1 : ∑ x : Bool × Fin 4, q x = 1 := by
    simp only [hqdef]; rw [Fintype.sum_prod_type]; simp
  have hqS : ∀ s : Bool, qS s = ∑ r : Fin 4, q (s, r) := by
    intro s; simp only [hqdef, hqSdef]; cases s <;> simp
  have herase : qS true = 1 := by simp [hqSdef]
  have hentq : entropy q = Real.log 4 := by
    simp only [hqdef, entropy]
    rw [Fintype.sum_prod_type]
    simp [Real.negMulLog]
  have hentp : entropy (fun y : Bool × Fin 4 => pS y.1 * gibbs 1 exampleEnergy y.2)
      = 2 * Real.negMulLog (9 / 20) + 6 * Real.negMulLog (1 / 60) := by
    simp only [hpSdef, entropy]
    rw [Fintype.sum_prod_type]
    simp [example_gibbs, Fin.sum_univ_four]
    ring_nf
  have hnum : 2 * Real.negMulLog (9 / 20) + 6 * Real.negMulLog (1 / 60) ≤ Real.log 4 := by
    have h1 : Real.log (9 / 20 : ℝ) = -Real.log (20 / 9) := by
      rw [show (9 / 20 : ℝ) = ((20 / 9 : ℝ))⁻¹ by norm_num, Real.log_inv]
    have h2 : Real.log (1 / 60 : ℝ) = -Real.log 60 := by
      rw [show (1 / 60 : ℝ) = ((60 : ℝ))⁻¹ by norm_num, Real.log_inv]
    have key : 9 * Real.log (20 / 9) + Real.log 60 ≤ 10 * Real.log 4 := by
      have hle : Real.log (((20 : ℝ) / 9) ^ 9 * 60) ≤ Real.log ((4 : ℝ) ^ 10) :=
        Real.log_le_log (by positivity) (by norm_num)
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow] at hle
      push_cast at hle
      linarith
    simp only [Real.negMulLog, h1, h2]
    linarith
  have hent : entropy (fun y : Bool × Fin 4 => pS y.1 * gibbs (1 / ((1 : ℝ) * 1)) exampleEnergy y.2)
      ≤ entropy q := by
    rw [hbeta, hentp, hentq]; exact hnum
  have hQ : (13 / 20) * Real.log 27
      = (∑ x : Bool × Fin 4, q x * exampleEnergy x.2)
        - ∑ r, gibbs (1 / ((1 : ℝ) * 1)) exampleEnergy r * exampleEnergy r := by
    rw [hbeta]
    simp only [hqdef]
    rw [Fintype.sum_prod_type]
    simp only [example_gibbs]
    simp [Fin.sum_univ_four, exampleEnergy]
    ring
  exact ⟨exampleEnergy, pS, q, qS, 13 / 20 * Real.log 27, hpS, hq0, hq1, hent, hqS, herase, hQ,
    landauer_principle 1 1 one_pos one_pos exampleEnergy false true (by simp) pS hpS q hq0 hq1
      hent qS hqS true herase _ hQ⟩

end Phys

