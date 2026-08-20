/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command; the header above is repeated below
-- as a module docstring.)

import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Finset

/-! ## Generalities on monochromatic cliques -/

section General

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

/-- The set of vertices of `W` adjacent to `v` in `G`. -/

lemma compl_comap {m n : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (G : SimpleGraph (Fin m)) : (G.comap f)ᶜ = Gᶜ.comap f := by
  ext a b
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun h => h1 (hf h), h2⟩, fun ⟨h1, h2⟩ => ⟨fun h => h1 (by rw [h]), h2⟩⟩

/-- The Ramsey property is monotone in the number of vertices. -/
