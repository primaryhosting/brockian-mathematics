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

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/

theorem G13_no_indep_five : ¬ ∃ t : Finset (Fin 13), G13ᶜ.IsNClique 5 t := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, ha, hb, hc, hd, he⟩ := exists_sorted_five ht.2
  have hne : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ G13.Adj x y := by
    intro x hx y hy hxy
    exact ((SimpleGraph.compl_adj G13 x y).1 (ht.1 hx hy hxy)).2
  have h := G13_no_indep5 a b c d e hab hbc hcd hde
  simp only [Bool.or_eq_true] at h
  have hfalse : ∀ x ∈ t, ∀ y ∈ t, x < y → adjB x y = false := by
    intro x hx y hy hxy
    have := hne x hx y hy (ne_of_lt hxy)
    simpa [G13] using this
  rw [hfalse a ha b hb hab, hfalse a ha c hc (hab.trans hbc),
    hfalse a ha d hd (hab.trans (hbc.trans hcd)),
    hfalse a ha e he (hab.trans (hbc.trans (hcd.trans hde))),
    hfalse b hb c hc hbc, hfalse b hb d hd (hbc.trans hcd),
    hfalse b hb e he (hbc.trans (hcd.trans hde)),
    hfalse c hc d hd hcd, hfalse c hc e he (hcd.trans hde),
    hfalse d hd e he hde] at h
  simp at h

/-! ### Monotonicity of the Ramsey property -/

/-- The set of `N` for which every graph on `Fin N` contains a triangle or an
independent set of size 5. -/
