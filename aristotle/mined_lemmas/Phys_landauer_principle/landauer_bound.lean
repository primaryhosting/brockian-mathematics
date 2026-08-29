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
