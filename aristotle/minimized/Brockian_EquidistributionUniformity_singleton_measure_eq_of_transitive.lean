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

import Mathlib

/-!
# Equidistribution from transitivity

If a group `G` acts transitively on a finite set `α`, then every `G`-invariant probability
measure on `α` is the uniform (equidistributed) measure: each singleton `{x}` receives mass
`1 / #α`.

The main result `sing_uniform_of_transitive` is stated unconditionally.  It is obtained from the
conditional statement `sing_uniform_of_constant_singleton_mass`, whose named hypothesis
(`hconst`: all singletons have the same mass) is discharged by
`singleton_measure_eq_of_transitive`.
-/

open MeasureTheory
open scoped ENNReal

namespace Brockian.EquidistributionUniformity

variable {G α : Type*}

/-- **Discharging lemma.**  For a transitive action of a group `G` on `α`, any `G`-invariant
measure assigns the same mass to any two singletons. -/

theorem singleton_measure_eq_of_transitive [Group G] [MulAction G α]
    [MulAction.IsPretransitive G α] [MeasurableSpace α]
    (μ : Measure α) [SMulInvariantMeasure G α μ] (x y : α) :
    μ {y} = μ {x} := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  have h := measure_preimage_smul (G := G) μ g {y}
  rw [← h, ← hg]
  congr 1
  ext z
  simp [smul_eq_iff_eq_inv_smul]

/-- **Conditional form.**  If a probability measure on a finite set gives all singletons the same
mass, then that common mass is `1 / #α`. -/
