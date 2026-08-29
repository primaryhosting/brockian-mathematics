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

theorem ngonChar_orthogonal (j l : ZMod n) (h1 : j ≠ l) (h2 : j ≠ -l) :
    charInner n (ngonChar n j) (ngonChar n l) = 0 := by
  have hjl : j - l ≠ 0 := sub_ne_zero_of_ne h1
  have hlj : l - j ≠ 0 := sub_ne_zero_of_ne (Ne.symm h1)
  have hpl : j + l ≠ 0 := by
    intro h; exact h2 (by linear_combination h)
  have hml : -j - l ≠ 0 := by
    intro h; exact h2 (by linear_combination -h)
  have hsum : ∑ x : DihedralGroup n, ngonChar n j x * (starRingEnd ℂ) (ngonChar n l x) = 0 := by
    rw [sum_dihedral]
    have hsr : ∀ k : ZMod n,
        ngonChar n j (sr k) * (starRingEnd ℂ) (ngonChar n l (sr k)) = 0 := by
      intro k; simp
    simp only [hsr, Finset.sum_const_zero, add_zero]
    have hterm : ∀ k : ZMod n,
        ngonChar n j (r k) * (starRingEnd ℂ) (ngonChar n l (r k))
          = chiN n ((j + l) * k) + chiN n ((j - l) * k)
            + chiN n ((-j - l) * k) + chiN n ((l - j) * k) := by
      intro k
      rw [ngonChar_r, ngonChar_r, conj_pair]
      have e1 : chiN n (j * k) * chiN n (l * k) = chiN n ((j + l) * k) := by
        rw [← chiN_add]; ring_nf
      have e2 : chiN n (j * k) * chiN n (-(l * k)) = chiN n ((j - l) * k) := by
        rw [← chiN_add]; ring_nf
      have e3 : chiN n (-(j * k)) * chiN n (l * k) = chiN n ((l - j) * k) := by
        rw [← chiN_add]; ring_nf
      have e4 : chiN n (-(j * k)) * chiN n (-(l * k)) = chiN n ((-j - l) * k) := by
        rw [← chiN_add]; ring_nf
      calc (chiN n (j * k) + chiN n (-(j * k))) * (chiN n (l * k) + chiN n (-(l * k)))
          = chiN n (j * k) * chiN n (l * k) + chiN n (j * k) * chiN n (-(l * k))
            + chiN n (-(j * k)) * chiN n (-(l * k))
            + chiN n (-(j * k)) * chiN n (l * k) := by ring
        _ = _ := by rw [e1, e2, e3, e4]
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_chiN, sum_chiN, sum_chiN, sum_chiN, if_neg hpl, if_neg hjl, if_neg hml, if_neg hlj]
    ring
  rw [charInner, hsum, mul_zero]

/-- **Multiplicity one.** The `j`-isotypic multiplicity of the two-dimensional representation
`ngonRep n j` inside the permutation representation on the `n` vertices of the regular `n`-gon
equals one, for every `j`. -/
