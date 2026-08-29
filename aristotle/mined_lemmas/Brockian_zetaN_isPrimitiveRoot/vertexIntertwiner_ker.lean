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

lemma vertexIntertwiner_ker (j : ZMod n) (hj : 2 * j ≠ 0) (u : Fin 2 → ℂ)
    (hu : Matrix.mulVec (vertexIntertwiner n j) u = 0) : u = 0 := by
  have hj' : -(2 * j) ≠ 0 := fun h => hj (by simpa using congrArg Neg.neg h)
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h0 : (n : ℂ) * u 0 = 0 := by
    have hs : ∑ a : ZMod n,
        chiN n (-(j * a)) * (Matrix.mulVec (vertexIntertwiner n j) u a) = 0 := by
      rw [hu]; simp
    have hterm : ∀ a : ZMod n,
        chiN n (-(j * a)) * (Matrix.mulVec (vertexIntertwiner n j) u a)
          = u 0 + chiN n ((-(2 * j)) * a) * u 1 := by
      intro a
      rw [vertexIntertwiner_mulVec]
      have e1 : chiN n (-(j * a)) * chiN n (j * a) = 1 := by
        rw [mul_comm]; exact chiN_mul_neg n (j * a)
      have e2 : chiN n (-(j * a)) * chiN n (-(j * a)) = chiN n ((-(2 * j)) * a) := by
        rw [← chiN_add]; ring_nf
      calc chiN n (-(j * a)) * (chiN n (j * a) * u 0 + chiN n (-(j * a)) * u 1)
          = (chiN n (-(j * a)) * chiN n (j * a)) * u 0
            + (chiN n (-(j * a)) * chiN n (-(j * a))) * u 1 := by ring
        _ = u 0 + chiN n ((-(2 * j)) * a) * u 1 := by rw [e1, e2, one_mul]
    simp only [hterm] at hs
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_chiN, if_neg hj'] at hs
    simpa [ZMod.card] using hs
  have h1 : (n : ℂ) * u 1 = 0 := by
    have hs : ∑ a : ZMod n,
        chiN n (j * a) * (Matrix.mulVec (vertexIntertwiner n j) u a) = 0 := by
      rw [hu]; simp
    have hterm : ∀ a : ZMod n,
        chiN n (j * a) * (Matrix.mulVec (vertexIntertwiner n j) u a)
          = chiN n ((2 * j) * a) * u 0 + u 1 := by
      intro a
      rw [vertexIntertwiner_mulVec]
      have e1 : chiN n (j * a) * chiN n (-(j * a)) = 1 := chiN_mul_neg n (j * a)
      have e2 : chiN n (j * a) * chiN n (j * a) = chiN n ((2 * j) * a) := by
        rw [← chiN_add]; ring_nf
      calc chiN n (j * a) * (chiN n (j * a) * u 0 + chiN n (-(j * a)) * u 1)
          = (chiN n (j * a) * chiN n (j * a)) * u 0
            + (chiN n (j * a) * chiN n (-(j * a))) * u 1 := by ring
        _ = chiN n ((2 * j) * a) * u 0 + u 1 := by rw [e1, e2, one_mul]
    simp only [hterm] at hs
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_chiN, if_neg hj] at hs
    simpa [ZMod.card] using hs
  funext c
  fin_cases c
  · simpa using (mul_eq_zero.mp h0).resolve_left hn
  · simpa using (mul_eq_zero.mp h1).resolve_left hn

/-- The intertwiner is injective when `2 * j ≠ 0`, so `ngonRep n j` occurs as an honest
two-dimensional subrepresentation of the vertex representation. -/
