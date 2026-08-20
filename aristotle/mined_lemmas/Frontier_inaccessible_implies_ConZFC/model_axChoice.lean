import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/

theorem model_axChoice (hκ : κ.IsInaccessible) : VSet κ.ord ⊨ axChoice := by
  rw [realize_axChoice]
  rintro x ⟨hne, hdisj⟩
  choose g hg using fun z : ↥((x : VSet κ.ord) : ZFSet) =>
    hne ⟨(z : ZFSet), mem_mem_V x.2 z.2⟩ z.2
  refine ⟨⟨ZFSet.range (fun z => ((g z : VSet κ.ord) : ZFSet)),
    range_mem_V hκ x.2 _ (fun z => (g z).2)⟩, ?_⟩
  intro z hz
  simp only [memR_VSet] at hz
  refine ⟨g ⟨(z : ZFSet), hz⟩, ⟨hg _, ZFSet.mem_range.2 ⟨⟨(z : ZFSet), hz⟩, rfl⟩⟩, ?_⟩
  rintro w' ⟨hw'z, hw'c⟩
  simp only [memR_VSet] at hw'z hw'c
  obtain ⟨z', hz'⟩ := ZFSet.mem_range.1 hw'c
  have hzz' : z = (⟨(z' : ZFSet), mem_mem_V x.2 z'.2⟩ : VSet κ.ord) := by
    rcases hdisj z hz ⟨(z' : ZFSet), mem_mem_V x.2 z'.2⟩ z'.2 with h | h
    · exact h
    · exact (h w' ⟨hw'z, by simpa only [memR_VSet, hz'] using hg z'⟩).elim
  have hval : ((z : VSet κ.ord) : ZFSet) = ((z' : ↥((x : VSet κ.ord) : ZFSet)) : ZFSet) :=
    congrArg Subtype.val hzz'
  have hidx : (⟨(z : ZFSet), hz⟩ : ↥((x : VSet κ.ord) : ZFSet)) = z' := Subtype.ext hval
  rw [hidx]
  exact Subtype.ext hz'.symm

