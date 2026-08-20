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

/-!
# The Conant–Ashby good regulator theorem

We formalize the deterministic, finite version of the theorem of Conant and Ashby:
*every good regulator of a system must be a model of that system*.

Setup: a system is a map `h : S → R → Z` sending a disturbance `s : S` and a regulatory
action `r : R` to an outcome `h s r : Z`.  A regulator is a (deterministic) map
`rho : S → R`; it is *successful* when the outcome is always the target value `z₀`.
Each disturbance `s` determines, through the system, the set `GoodActions h z₀ s` of actions
that keep the outcome on target — this is the information about the system that a regulator
could possibly need.  A *good regulator* is a successful regulator of minimal Shannon entropy
(the "simplest" successful regulator) with respect to a strictly positive weighting `p` of the
disturbances.

The theorem `Frontier.good_regulator` states that such a regulator is a **model** of the
system: its action is a function of the system's own map `s ↦ GoodActions h z₀ s`, i.e.
`rho` factors as `m ∘ (GoodActions h z₀)`.
-/

namespace Frontier

variable {S R Z : Type*} [Fintype S] [DecidableEq S] [Fintype R] [DecidableEq R]

/-- The total weight of the disturbances that the regulator `rho` maps to the state `r`. -/

theorem good_regulator_apply_eq {p : S → ℝ} {h : S → R → Z} {z₀ : Z} {rho : S → R}
    (hp : ∀ s, 0 < p s) (hg : GoodRegulator p h z₀ rho) {s t : S}
    (hst : GoodActions h z₀ s = GoodActions h z₀ t) : rho s = rho t := by
  by_contra hne
  obtain ⟨hsucc, hmin⟩ := hg
  have hs_ne_t : s ≠ t := by rintro rfl; exact hne rfl
  have hmem1 : rho s ∈ GoodActions h z₀ t := by rw [← hst]; exact hsucc s
  have hmem2 : rho t ∈ GoodActions h z₀ s := by rw [hst]; exact hsucc t
  set A := Function.update rho t (rho s) with hAdef
  set B := Function.update rho s (rho t) with hBdef
  have hA : Successful h z₀ A := by
    intro u
    by_cases hu : u = t
    · subst hu; rw [hAdef, Function.update_self]; exact hmem1
    · rw [hAdef, Function.update_of_ne hu]; exact hsucc u
  have hB : Successful h z₀ B := by
    intro u
    by_cases hu : u = s
    · subst hu; rw [hBdef, Function.update_self]; exact hmem2
    · rw [hBdef, Function.update_of_ne hu]; exact hsucc u
  have hpos : 0 < p s + p t := by have := hp s; have := hp t; linarith
  set lam : ℝ := p s / (p s + p t) with hlam
  set mu : ℝ := p t / (p s + p t) with hmu
  have hlam0 : 0 < lam := div_pos (hp s) hpos
  have hmu0 : 0 < mu := div_pos (hp t) hpos
  have hsum1 : lam + mu = 1 := by rw [hlam, hmu, ← add_div, div_self hpos.ne']
  have hAm : ∀ r, regMass p A r
      = regMass p rho r + (if rho s = r then p t else 0) - (if rho t = r then p t else 0) := by
    intro r; rw [hAdef, regMass_update]
  have hBm : ∀ r, regMass p B r
      = regMass p rho r + (if rho t = r then p s else 0) - (if rho s = r then p s else 0) := by
    intro r; rw [hBdef, regMass_update]
  -- the state distribution of `rho` is a strict convex combination of those of `A` and `B`
  have hconv : ∀ r, lam * regMass p A r + mu * regMass p B r = regMass p rho r := by
    intro r
    rw [hAm, hBm, hlam, hmu]
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hne
    · field_simp; ring
    · field_simp; ring
    · field_simp; ring
  have hAnn : ∀ r, 0 ≤ regMass p A r := regMass_nonneg (fun s => (hp s).le) A
  have hBnn : ∀ r, 0 ≤ regMass p B r := regMass_nonneg (fun s => (hp s).le) B
  have hdiff : regMass p A (rho s) ≠ regMass p B (rho s) := by
    rw [hAm, hBm]
    simp only [if_neg (Ne.symm hne)]
    have := hp s; have := hp t
    intro hcon; simp at hcon; linarith
  -- strict concavity of the entropy then contradicts minimality
  have hkey : lam * regEntropy p A + mu * regEntropy p B < regEntropy p rho := by
    unfold regEntropy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_lt_sum ?_ ⟨rho s, Finset.mem_univ _, ?_⟩
    · intro r _
      have := Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 (hAnn r)) (Set.mem_Ici.2 (hBnn r))
        hlam0.le hmu0.le hsum1
      simpa [smul_eq_mul, hconv r] using this
    · have := Real.strictConcaveOn_negMulLog.2 (Set.mem_Ici.2 (hAnn (rho s)))
        (Set.mem_Ici.2 (hBnn (rho s))) hdiff hlam0 hmu0 hsum1
      simpa [smul_eq_mul, hconv (rho s)] using this
  have h1 := mul_le_mul_of_nonneg_left (hmin A hA) hlam0.le
  have h2 := mul_le_mul_of_nonneg_left (hmin B hB) hmu0.le
  have h3 : regEntropy p rho = (lam + mu) * regEntropy p rho := by rw [hsum1]; ring
  nlinarith [h1, h2, h3, hkey]

/-- **Conant–Ashby good regulator theorem** (deterministic, finite version).

Every good regulator of a system contains a model of that system: the action taken by a
successful regulator of minimal entropy depends on the disturbance only through the system's
own map `s ↦ GoodActions h z₀ s`, so it factors as `rho = m ∘ GoodActions h z₀`. -/
