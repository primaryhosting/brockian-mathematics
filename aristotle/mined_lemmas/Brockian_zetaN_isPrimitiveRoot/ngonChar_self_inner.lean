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

theorem ngonChar_self_inner (j : ZMod n) (hj : 2 * j ≠ 0) :
    charInner n (ngonChar n j) (ngonChar n j) = 1 := by
  have hj' : -(2 * j) ≠ 0 := fun h => hj (by simpa using congrArg Neg.neg h)
  have hsum : ∑ x : DihedralGroup n, ngonChar n j x * (starRingEnd ℂ) (ngonChar n j x)
      = 2 * n := by
    rw [sum_dihedral]
    have hsr : ∀ k : ZMod n,
        ngonChar n j (sr k) * (starRingEnd ℂ) (ngonChar n j (sr k)) = 0 := by
      intro k; simp
    simp only [hsr, Finset.sum_const_zero, add_zero]
    have hterm : ∀ k : ZMod n,
        ngonChar n j (r k) * (starRingEnd ℂ) (ngonChar n j (r k))
          = chiN n ((2 * j) * k) + 1 + 1 + chiN n ((-(2 * j)) * k) := by
      intro k
      rw [ngonChar_r, conj_pair]
      have e1 : chiN n (j * k) * chiN n (j * k) = chiN n ((2 * j) * k) := by
        rw [← chiN_add]; ring_nf
      have e2 : chiN n (-(j * k)) * chiN n (-(j * k)) = chiN n ((-(2 * j)) * k) := by
        rw [← chiN_add]; ring_nf
      have e3 : chiN n (j * k) * chiN n (-(j * k)) = 1 := chiN_mul_neg n (j * k)
      have e4 : chiN n (-(j * k)) * chiN n (j * k) = 1 := by rw [mul_comm]; exact e3
      calc (chiN n (j * k) + chiN n (-(j * k))) * (chiN n (j * k) + chiN n (-(j * k)))
          = chiN n (j * k) * chiN n (j * k) + chiN n (j * k) * chiN n (-(j * k))
            + chiN n (-(j * k)) * chiN n (j * k)
            + chiN n (-(j * k)) * chiN n (-(j * k)) := by ring
        _ = chiN n ((2 * j) * k) + 1 + 1 + chiN n ((-(2 * j)) * k) := by
            rw [e1, e2, e3, e4]
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_chiN, sum_chiN, if_neg hj, if_neg hj']
    simp [ZMod.card]
    ring
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [charInner, hsum, card_dihedral_ne_zero]
  field_simp

/-- Distinct `j`'s (up to sign) give orthogonal characters, hence inequivalent representations. -/
