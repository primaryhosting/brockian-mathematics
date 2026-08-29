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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/

theorem H_no_indep_five : ∀ S : Finset (Fin 13), ¬ Hᶜ.IsNClique 5 S := by
  rintro S ⟨hclique, hcard⟩
  have hnadj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → hb x y = false := by
    intro x hx y hy hxy
    have := hclique (by exact_mod_cast hx) (by exact_mod_cast hy) hxy
    rw [SimpleGraph.compl_adj] at this
    simpa [H] using this.2
  have hlen : (S.sort (· ≤ ·)).length = 5 := by rw [Finset.length_sort, hcard]
  have hpair : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort S)
  have hmem : ∀ x, x ∈ S.sort (· ≤ ·) → x ∈ S := fun x hx => (Finset.mem_sort _).mp hx
  match hl : S.sort (· ≤ ·), hlen, hpair, hmem with
  | [a, b, c, d, e], _, hp, hm =>
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hp
      have ha : a ∈ S := hm a (by simp)
      have hbS : b ∈ S := hm b (by simp)
      have hcS : c ∈ S := hm c (by simp)
      have hdS : d ∈ S := hm d (by simp)
      have heS : e ∈ S := hm e (by simp)
      obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde, -⟩ := hp
      exact no_indep5 a b hab (hnadj a ha b hbS (ne_of_lt hab))
        c hbc (hnadj a ha c hcS (ne_of_lt hac)) (hnadj b hbS c hcS (ne_of_lt hbc))
        d hcd (hnadj a ha d hdS (ne_of_lt had)) (hnadj b hbS d hdS (ne_of_lt hbd))
        (hnadj c hcS d hdS (ne_of_lt hcd))
        e hde (hnadj a ha e heS (ne_of_lt hae)) (hnadj b hbS e heS (ne_of_lt hbe))
        (hnadj c hcS e heS (ne_of_lt hce)) (hnadj d hdS e heS (ne_of_lt hde))

/-- Cliques transfer along an injective map by taking images. -/
