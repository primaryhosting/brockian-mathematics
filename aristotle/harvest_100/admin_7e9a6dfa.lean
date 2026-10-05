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
  Target theorem `not_admissible_of_residueImage_univ` for the corpus module
  `Brockian.AdmissibilityHLCriterion`.

  The corpus modules are not part of this project, so the three corpus definitions the
  goal is phrased in terms of (`residueImage`, `OmitsResidue`, `Admissible`) are
  reproduced here verbatim, in their original namespace, purely so that the statement
  elaborates.  Nothing else from the corpus is restated or re-proved.

  The statement mentions `Finset.univ : Finset (ZMod p)` for a `p` that is only known to
  be prime through the ordinary hypothesis `hp : p.Prime`, so the ambient environment has
  to be able to see `Fintype (ZMod p)`.  The two `attribute` commands below make the
  primality hypothesis usable by instance search (`Nat.Prime` unfolds to `Irreducible`),
  which supplies `NeZero p` and hence the canonical `Fintype (ZMod p)`.  This is only
  scaffolding for elaboration; it adds no assumption.
-/

attribute [class] Irreducible

set_option allowUnsafeReducibility true in
attribute [reducible] Nat.Prime

instance neZeroOfNatIrreducible {p : ℕ} [hp : Irreducible p] : NeZero p :=
  ⟨(Nat.Prime.pos hp).ne'⟩

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `H` *omits a residue class* mod `p`: some residue mod `p` is not occupied by `H`. -/
def OmitsResidue (p : ℕ) (H : Finset ℤ) : Prop :=
  ∃ r : ZMod p, r ∉ residueImage p H

/-- **Admissibility (Hardy–Littlewood).** A finite integer tuple `H` is admissible iff
for every prime `p` it omits at least one residue class mod `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → OmitsResidue p H

/-- If, at some prime `p`, a finite integer set `S` occupies *every* residue class mod
`p`, then `S` is not admissible: admissibility would provide a residue `r` outside the
image, contradicting that the image is all of `ZMod p`. -/
theorem not_admissible_of_residueImage_univ {p : ℕ} (hp : p.Prime) {S : Finset ℤ}
    (h : residueImage p S = Finset.univ) : ¬ Admissible S := by
  intro hadm
  obtain ⟨r, hr⟩ := hadm p hp
  exact hr (h ▸ Finset.mem_univ r)

end Brockian.AdmissibilityHLCriterion

