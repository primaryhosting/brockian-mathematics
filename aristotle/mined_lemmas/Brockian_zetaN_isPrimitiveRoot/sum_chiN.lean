import Mathlib
/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The classical "pentagon" facts about the dihedral group `D₅` (the symmetry group of a regular
pentagon) are:

* `D₅` has two irreducible two-dimensional complex representations `ρ₁`, `ρ₂`, obtained by letting
  the rotation `r` act as a rotation by `2π/5` resp. `4π/5`;
* they are pairwise inequivalent;
* the permutation representation of `D₅` on the five vertices of the pentagon contains each of
  them with multiplicity exactly one — i.e. each `ρⱼ`-isotypic component of the vertex
  representation is exactly two-dimensional.

This file generalises all of this to an arbitrary regular `n`-gon.  For every `j : ZMod n` we build
a genuine two–dimensional complex representation `Brockian.ngonRep n j` of `DihedralGroup n`, and we
compute its character `Brockian.ngonChar n j`.  We then show, purely by character computations:

* `ngonChar n j` has norm one (so `ngonRep n j` is irreducible) as soon as `2 * j ≠ 0`;
* `ngonChar n j` and `ngonChar n l` are orthogonal when `j ≠ l` and `j ≠ -l`;
* the character of the vertex permutation representation pairs to `1` against every `ngonChar n j`,
  i.e. the multiplicity of `ρⱼ` in the vertex representation is one for every `j`.

Specialising to `n = 5` recovers the pentagon statements.
-/

open Complex DihedralGroup

namespace Brockian

section Roots

/-- A primitive `n`-th root of unity in `ℂ`. -/

lemma sum_chiN (n : ℕ) [NeZero n] (m : ZMod n) :
    ∑ k : ZMod n, chiN n (m * k) = if m = 0 then (n : ℂ) else 0 := by
  classical
  have h : ∀ k : ZMod n, chiN n (m * k) = (AddChar.mulShift (chiN n) m) k := fun _ => rfl
  simp only [h]
  rw [AddChar.sum_eq_ite]
  by_cases hm : m = 0
  · subst hm
    have hz : AddChar.mulShift (chiN n) 0 = 0 := by
      ext x; simp [AddChar.mulShift]
    rw [if_pos hz, if_pos rfl]
    simp
  · rw [if_neg hm, if_neg]
    intro hc
    refine hm ?_
    rw [← chiN_eq_one_iff n m]
    have := congrArg (fun f : AddChar (ZMod n) ℂ => f 1) hc
    simpa [AddChar.mulShift] using this

end Roots

section Dihedral

variable (n : ℕ) [NeZero n]

/-- Splitting a sum over `DihedralGroup n` into the rotations and the reflections. -/
