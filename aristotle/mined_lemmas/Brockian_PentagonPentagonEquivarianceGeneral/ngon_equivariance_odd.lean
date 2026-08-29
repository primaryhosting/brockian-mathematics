/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the text is otherwise verbatim.)

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

namespace Brockian

open DihedralGroup

/-!
## The dihedral action on the vertices of the `n`-gon

We label the vertices of the regular `n`-gon by `ZMod n`.  With Mathlib's multiplication
convention on `DihedralGroup n` (`r i * sr j = sr (j - i)`), the natural *left* action of the
symmetry group on the vertex set is given by

* `r i • x = x - i`   (rotation),
* `sr i • x = i - x`  (reflection).
-/

/-- The action of a symmetry of the regular `n`-gon on its vertex set `ZMod n`. -/

theorem ngon_equivariance_odd {n : ℕ} (hn : Odd n) (f : ZMod n → ZMod n)
    (h : ∀ (g : DihedralGroup n) (x : ZMod n), f (g • x) = g • f x) :
    ∀ x, f x = x := by
  obtain ⟨c, hc, hf⟩ := (PentagonPentagonEquivarianceGeneral f).1 h
  have hc0 : c = 0 := by
    have h2 : (2 : ZMod n) * c = 0 := by linear_combination (norm := ring_nf) hc
    have : IsUnit (2 : ZMod n) := by
      have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
      simpa using (ZMod.isUnit_iff_coprime 2 n).2 (by simpa [Nat.Coprime] using hcop)
    obtain ⟨u, hu⟩ := this
    have := congrArg (fun z => (↑u⁻¹ : ZMod n) * z) h2
    simpa [← hu, ← mul_assoc, ← Units.val_mul] using this
  intro x
  simp [hf, hc0]

/-- The pentagon case (`n = 5`), recovering the original `D₅` statement. -/
