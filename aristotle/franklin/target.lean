import Mathlib

/-
  Brockian/PentagonalPartition.lean — GENERALIZED PENTAGONAL NUMBERS
  and the Euler pentagonal ↔ partition bridge (Aug 1).

  The headline question "what connects Euler's pentagonal number theorem to
  Ramanujan's partitions" is the pentagonal number theorem:

        ∏_{n≥1} (1 − xⁿ)  =  ∑_{k∈ℤ} (−1)ᵏ x^{k(3k−1)/2},

  equivalently the partition recurrence
        p(n) = ∑_{k≠0} (−1)^{k−1} p(n − g_k),   g_k = k(3k−1)/2.

  This module formalizes the ARITHMETIC SPINE that both sides share: the
  generalized pentagonal number function g_k = k(3k−1)/2 as a total ℤ→ℤ map,
  proved well-defined (the numerator is always even), together with its
  structural laws — the doubling identity, nonnegativity, the reflection
  g_{−k} = g_k + k, the successor recurrence, strict growth, and (a genuinely
  non-trivial fact) global INJECTIVITY of g over ℤ, which is exactly what makes
  the exponents 0,1,2,5,7,12,15,… on the right-hand side pairwise distinct.

  The one honest tie to real partitions available at Mathlib 4.32 is the base
  count p(0) = 1, discharged against Mathlib's own `Nat.Partition`.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `pent`                — g_k = k(3k−1)/2 as a function ℤ → ℤ.
  * `two_dvd_pentNum`     — 2 ∣ k(3k−1): the numerator is always even, so the
                            division defining `pent` is exact (no ℤ-div collapse).
  * `two_mul_pent`        — 2 · g_k = k(3k−1): the exact doubling identity.
  * `two_mul_pent_expand` — 2 · g_k = 3k² − k.
  * `pent_nonneg`         — 0 ≤ g_k for every integer k.
  * `pent_reflect`        — g_{−k} = g_k + k  (pairs the two arms k, −k).
  * `pent_succ`           — g_{k+1} = g_k + (3k+1)  (the classic step recurrence).
  * `pent_lt_succ`        — g_k < g_{k+1} for k ≥ 0  (strict growth on the arm).
  * `pent_injective`      — g is injective on ℤ ⇒ the PST exponents are distinct.
  * `partition_zero_card` — Fintype.card (Nat.Partition 0) = 1, i.e. p(0) = 1,
                            anchored on Mathlib's `Nat.Partition`.

  ## COMPUTATION  (values discharged via the doubling identity, PROVED, not by
      trusting a kernel oracle — listed here because they are concrete instances)
  * `pent_values`         — g at k = 0,1,−1,2,−2,3,−3 equals 0,1,2,5,7,12,15,
                            the first generalized pentagonal numbers in order.

  ## What is NOT proved  (precise obstructions at Mathlib 4.32)
  * The pentagonal number theorem itself (the ∏(1−xⁿ) = ∑(−1)ᵏx^{g_k} identity,
    Franklin's involution) — Mathlib has `Nat.Partition` and Euler's
    odd = distinct theorem, but NOT the pentagonal number theorem nor the
    generating-function product ∏(1−xⁿ); a from-scratch Franklin involution is
    out of scope here.
  * The partition recurrence p(n) = ∑_{k≠0}(−1)^{k−1} p(n−g_k) — it is
    equivalent to the theorem above, so equally out of reach.
  * Partition counts p(n) for n ≥ 1 by evaluation — `Fintype.card (Nat.Partition n)`
    does NOT reduce under `decide` at Mathlib 4.32 (its `Fintype` instance is built
    through non-reducing `Multiset`/`Finset` machinery). Only p(0)=1 is reachable
    cheaply (via the `Unique (Nat.Partition 0)` instance).

  ## Relation to the C₅ spectral work in this repo
  NONE that is rigorous. Pentagonal numbers and the C₅/D₅ spectral modules share
  only the informal "five / pentagon" motif (a pentagon has 5 sides; nested
  pentagons count pentagonal numbers). There is no theorem here linking g_k to
  the cyclic-group Laplacian spectrum, and none is claimed.
-/

set_option autoImplicit false

namespace Brockian.PentagonalPartition

/-- The generalized pentagonal number `g_k = k(3k−1)/2`, as a total map `ℤ → ℤ`.
Ordinary pentagonal numbers are the values at `k = 1, 2, 3, …`; the values at
`k = 0, ±1, ±2, …` enumerate the exponents in Euler's pentagonal number theorem. -/
def pent (k : ℤ) : ℤ := k * (3 * k - 1) / 2

/-- The numerator `k(3k−1)` is always even, so `pent` divides exactly (no ℤ-division
collapse). This is the well-definedness fact behind the `/2`. -/
theorem two_dvd_pentNum (k : ℤ) : 2 ∣ k * (3 * k - 1) := by
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- k = m + m
    exact ⟨m * (3 * (m + m) - 1), by rw [hm]; ring⟩
  · -- k = 2m + 1
    exact ⟨(2 * m + 1) * (3 * m + 1), by rw [hm]; ring⟩

/-- The exact doubling identity `2 · g_k = k(3k−1)`. Every structural fact below is
derived from this, so nothing depends on how `ediv` rounds. -/
theorem two_mul_pent (k : ℤ) : 2 * pent k = k * (3 * k - 1) :=
  Int.mul_ediv_cancel' (two_dvd_pentNum k)

/-- Expanded doubling identity `2 · g_k = 3k² − k`. -/
theorem two_mul_pent_expand (k : ℤ) : 2 * pent k = 3 * k ^ 2 - k := by
  rw [two_mul_pent]; ring

/-- Generalized pentagonal numbers are nonnegative: `0 ≤ g_k` for all `k ∈ ℤ`. -/
theorem pent_nonneg (k : ℤ) : 0 ≤ pent k := by
  have h : 2 * pent k = k * (3 * k - 1) := two_mul_pent k
  have hk : 0 ≤ k * (3 * k - 1) := by nlinarith [sq_nonneg k, sq_nonneg (k - 1)]
  nlinarith [h, hk]

/-- Reflection law `g_{−k} = g_k + k`: this is exactly why the two arms `k` and
`−k` of the pentagonal sum land on adjacent exponents (e.g. `g_2 = 5`, `g_{−2} = 7`). -/
theorem pent_reflect (k : ℤ) : pent (-k) = pent k + k := by
  have h1 : 2 * pent (-k) = (-k) * (3 * (-k) - 1) := two_mul_pent (-k)
  have h2 : 2 * pent k = k * (3 * k - 1) := two_mul_pent k
  nlinarith [h1, h2]

/-- Successor recurrence `g_{k+1} = g_k + (3k+1)`: the classic step law for
pentagonal numbers (`1 → 5 → 12 → 22 → …` on the positive arm). -/
theorem pent_succ (k : ℤ) : pent (k + 1) = pent k + (3 * k + 1) := by
  have h1 : 2 * pent (k + 1) = (k + 1) * (3 * (k + 1) - 1) := two_mul_pent (k + 1)
  have h2 : 2 * pent k = k * (3 * k - 1) := two_mul_pent k
  nlinarith [h1, h2]

/-- Strict growth on the nonnegative arm: `g_k < g_{k+1}` whenever `0 ≤ k`. -/
theorem pent_lt_succ {k : ℤ} (hk : 0 ≤ k) : pent k < pent (k + 1) := by
  rw [pent_succ]; linarith

/-- **Injectivity of `g` over `ℤ`.** Distinct integers give distinct generalized
pentagonal numbers; equivalently the exponents `0,1,2,5,7,12,15,…` on the
right-hand side of the pentagonal number theorem are pairwise distinct. -/
theorem pent_injective : Function.Injective pent := by
  intro a b h
  have ha : 2 * pent a = a * (3 * a - 1) := two_mul_pent a
  have hb : 2 * pent b = b * (3 * b - 1) := two_mul_pent b
  -- From `pent a = pent b` we get `(a − b)·(3(a+b) − 1) = 0`.
  have key : (a - b) * (3 * (a + b) - 1) = 0 := by nlinarith [ha, hb, h]
  rcases mul_eq_zero.mp key with hab | hodd
  · exact sub_eq_zero.mp hab
  · -- `3(a+b) − 1 = 0` has no integer solution.
    omega

/-- The first generalized pentagonal numbers, in the classic PST order
`k = 0, 1, −1, 2, −2, 3, −3`, are `0, 1, 2, 5, 7, 12, 15` — the exponents of
`∏(1−xⁿ) = 1 − x − x² + x⁵ + x⁷ − x¹² − x¹⁵ + …`. Each value is PROVED from the
doubling identity (not asserted). -/
theorem pent_values :
    pent 0 = 0 ∧ pent 1 = 1 ∧ pent (-1) = 2 ∧ pent 2 = 5 ∧
      pent (-2) = 7 ∧ pent 3 = 12 ∧ pent (-3) = 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · first
      | (have h := two_mul_pent 0; omega)
      | (have h := two_mul_pent 1; omega)
      | (have h := two_mul_pent (-1); omega)
      | (have h := two_mul_pent 2; omega)
      | (have h := two_mul_pent (-2); omega)
      | (have h := two_mul_pent 3; omega)
      | (have h := two_mul_pent (-3); omega)

/-- Partition base count `p(0) = 1`, discharged against Mathlib's own
`Nat.Partition`: the empty partition is the unique partition of `0`. This is the
one honest contact point with real partition theory available at Mathlib 4.32. -/
theorem partition_zero_card : Fintype.card (Nat.Partition 0) = 1 := by
  rw [Fintype.card_eq_one_iff_nonempty_unique]
  exact ⟨inferInstance⟩

end Brockian.PentagonalPartition

/-
  Brockian/PentagonalTheoremFranklin.lean — THE PENTAGONAL NUMBER THEOREM,
  reduced to Franklin's involution (Aug 1).

  `Brockian/PentagonalPartition.lean` proved the ARITHMETIC SPINE of Euler's
  pentagonal number theorem (the generalized pentagonal numbers g_k = k(3k−1)/2,
  their exact doubling law, injectivity ⇒ distinct exponents, and p(0)=1). It
  left OPEN the theorem itself:

        ∏_{n≥1} (1 − xⁿ)  =  ∑_{k∈ℤ} (−1)ᵏ x^{g_k}.

  This module pushes that program to the exact frontier reachable at Mathlib
  4.32. Mathlib provides the generating-function apparatus for partitions
  (`Nat.Partition.genFun`, `genFun_eq_tprod`, `distincts`) and the pentagonal
  function `pentagonal : ℤ → ℕ` — but its `Pentagonal.lean` explicitly lists the
  pentagonal number theorem as a `TODO`, and Franklin's sign-reversing
  involution is ABSENT from the library.

  We do the honest thing: we PROVE the entire chain up to Franklin, isolating the
  one missing combinatorial fact as a single, precisely-stated named hypothesis.

  The engine is a character choice. For `pstChar i c = if c = 1 then −1 else 0`,
  Mathlib's `genFun pstChar` is (proved here) exactly the pentagonal product
  `∏_{i≥1}(1 − xⁱ)`, and its `n`-th coefficient is (proved here) the SIGNED COUNT

        ∑_{p ⊢ n, p distinct} (−1)^{#parts(p)}

  (partitions into an even number of distinct parts, minus those into an odd
  number). Franklin's number-theoretic theorem is precisely the assertion that
  this signed count collapses to `(−1)ᵏ` when `n = g_k` and to `0` otherwise —
  i.e. it equals `pentCoeff n`. THAT collapse is the sole remaining obstruction,
  named `hFranklin` below. It is a TRUE statement (so the conditional theorems are
  not vacuous), but proving it requires constructing Franklin's involution, which
  Mathlib does not have.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `pstChar`                    — the Euler-product character `if c = 1 then −1 else 0`.
  * `prod_pstChar_eq`            — for a partition `p`, the character product equals
                                   `(−1)^{#parts}` if `p` has distinct parts, else `0`
                                   (a non-distinct partition contributes nothing).
  * `coeff_genFun_pstChar`       — **the coefficient identity**: the `n`-th coefficient of
                                   `genFun pstChar` equals `∑_{p ∈ distincts n} (−1)^{#parts}`.
  * `genFun_pstChar_eq_prod`     — **the product identity**: `genFun pstChar = ∏'ᵢ (1 − Xⁱ⁺¹)`,
                                   i.e. `genFun pstChar` really IS Euler's pentagonal product
                                   `∏_{n≥1}(1 − xⁿ)` in `ℤ⟦X⟧`.
  * `natCast_pentagonal_eq_pent` — bridge: Mathlib's `pentagonal k` (ℕ) cast to ℤ equals the
                                   repo's own `Brockian.PentagonalPartition.pent k`.
  * `pentSign`, `pentCoeff`      — the RHS coefficient `(−1)ᵏ` at `g_k`, else `0` (well-defined
                                   because `pentagonal` is injective).
  * `pentagonalNumberTheorem_of_franklin`  — **PST, conditional on Franklin.** Given the named
                                   hypothesis `hFranklin` (the signed distinct-count equals
                                   `pentCoeff`), the coefficient of `genFun pstChar` is `pentCoeff n`.
  * `pentagonalProduct_coeff_of_franklin`  — the same conclusion phrased on the actual product
                                   `∏'ᵢ(1 − Xⁱ⁺¹)`, via the product identity.

  ## What is NOT proved  (the single remaining obstruction)
  * `hFranklin` itself — Franklin's sign-reversing involution. Concretely, the statement
        `∀ m, (∑ p ∈ Nat.Partition.distincts m, (−1)^{#parts p}) = pentCoeff m`
    is TRUE but UNPROVED here. It is the assertion that the involution on distinct
    partitions (move the smallest part vs. peel the top diagonal) pairs off all
    distinct partitions of `m` with opposite `(−1)^{#parts}` sign, except for the two
    pentagonal fixed-point families, which survive with sign `(−1)ᵏ`. This is why the
    two theorems above are stated with `hFranklin` as an explicit hypothesis and are
    named `..._of_franklin` — they are NOT the unconditional theorem.

  ## Precise remaining obstruction (exact missing Mathlib combinatorics)
  Mathlib 4.32 has NO sign-reversing involution on `Nat.Partition.distincts` and no
  form of the pentagonal number theorem (`Mathlib/Combinatorics/Enumerative/Pentagonal.lean`
  states it as a `TODO`). The missing lemma is exactly:

      theorem franklin (m : ℕ) :
          (∑ p ∈ Nat.Partition.distincts m, (-1 : ℤ) ^ (Multiset.card p.parts))
            = pentCoeff m

  Proving it needs: (i) the Durfee/staircase statistics `s(p)` = smallest part and
  `t(p)` = length of the top boundary diagonal on a distinct partition; (ii) the
  Franklin map that either removes the smallest part and lengthens the diagonal, or
  the reverse, changing `#parts` by exactly one (hence flipping the sign); (iii) the
  proof that this map is an involution whose only fixed points occur when `s = t` (or
  `s = t+1`) with `m = g_k`, forcing all non-pentagonal signed contributions to
  cancel. None of this data exists in Mathlib; constructing it is a substantial
  combinatorial development beyond a single module.
-/

set_option autoImplicit false

namespace Brockian.PentagonalTheoremFranklin

open Nat.Partition PowerSeries Finset

/-- The Euler-product character `f(i, c) = if c = 1 then −1 else 0`. Feeding this to
Mathlib's `Nat.Partition.genFun` builds the pentagonal product `∏(1 − xⁱ)`: the factor
for part `i` becomes `1 + (−1)·xⁱ = 1 − xⁱ`, and only partitions with all parts
distinct (every count `= 1`) survive with a nonzero character product. -/
def pstChar : ℕ → ℕ → ℤ := fun _ c => if c = 1 then (-1 : ℤ) else 0

/-- The character product over a partition `p`: it equals `(−1)^{#parts}` when the parts
are all distinct, and `0` otherwise (a repeated part gives a `0` factor). This is the
combinatorial heart of the Euler product: only distinct partitions contribute, each
weighted by the parity of its number of parts. -/
theorem prod_pstChar_eq {n : ℕ} (p : n.Partition) :
    p.parts.toFinsupp.prod pstChar =
      if p.parts.Nodup then (-1 : ℤ) ^ (Multiset.card p.parts) else 0 := by
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  by_cases h : p.parts.Nodup
  · rw [if_pos h]
    have hval : ∀ i ∈ p.parts.toFinset, pstChar i (p.parts.count i) = (-1 : ℤ) := by
      intro i hi
      rw [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_one_of_mem h hi]
      simp [pstChar]
    rw [Finset.prod_congr rfl hval, Finset.prod_const, Multiset.toFinset_card_of_nodup h]
  · rw [if_neg h]
    rw [Multiset.nodup_iff_count_le_one] at h
    simp only [not_forall, not_le] at h
    obtain ⟨a, ha⟩ := h
    refine Finset.prod_eq_zero (i := a) ?_ ?_
    · rw [Multiset.mem_toFinset]
      exact Multiset.count_pos.mp (by omega)
    · have hne : p.parts.count a ≠ 1 := by omega
      simp [pstChar, hne]

/-- **The coefficient identity.** The `n`-th coefficient of `genFun pstChar` is the signed
count of partitions of `n` into distinct parts, weighted by `(−1)^{#parts}`. Equivalently:
`#{distinct partitions of n with an even number of parts} − #{… odd number of parts}`.
This is exactly the coefficient of `xⁿ` in Euler's product `∏_{i≥1}(1 − xⁱ)`. -/
theorem coeff_genFun_pstChar (n : ℕ) :
    (genFun pstChar).coeff n = ∑ p ∈ distincts n, (-1 : ℤ) ^ (Multiset.card p.parts) := by
  rw [coeff_genFun]
  simp_rw [prod_pstChar_eq]
  rw [distincts, Finset.sum_filter]

open scoped PowerSeries.WithPiTopology in
/-- **The product identity.** `genFun pstChar` is literally Euler's pentagonal product
`∏_{i≥1}(1 − xⁱ)` in `ℤ⟦X⟧`. Together with `coeff_genFun_pstChar`, this shows the
coefficient of `xⁿ` in `∏(1 − xⁱ)` is the signed distinct-partition count. -/
theorem genFun_pstChar_eq_prod :
    genFun pstChar = ∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)) := by
  rw [genFun_eq_tprod]
  refine tprod_congr (fun i => ?_)
  rw [sub_eq_add_neg]
  congr 1
  rw [tsum_eq_single 0]
  · rw [smul_eq_C_mul]
    simp [pstChar]
  · intro j hj
    rw [smul_eq_C_mul]
    simp [pstChar, hj]

/-- Bridge to the repo's own definition: Mathlib's `pentagonal k` (an `ℕ`), cast to `ℤ`,
equals `Brockian.PentagonalPartition.pent k = k(3k−1)/2`. This ties the exponents used
here to the injective generalized-pentagonal function proved in `PentagonalPartition`. -/
theorem natCast_pentagonal_eq_pent (k : ℤ) :
    (pentagonal k : ℤ) = Brockian.PentagonalPartition.pent k := by
  rw [natCast_pentagonal]; rfl

/-- The sign `(−1)ᵏ` attached to the exponent `g_k`. -/
def pentSign (k : ℤ) : ℤ := if Even k then 1 else -1

open Classical in
/-- The right-hand-side coefficient of the pentagonal number theorem: the coefficient of
`xⁿ` in `∑_{k∈ℤ} (−1)ᵏ x^{g_k}`. Because `pentagonal` is injective (Mathlib's
`pentagonal_injective`, matching `PentagonalPartition.pent_injective`), at most one `k`
has `g_k = n`, so this is `(−1)ᵏ` when `n` is generalized-pentagonal with index `k`, and
`0` otherwise. -/
noncomputable def pentCoeff (n : ℕ) : ℤ :=
  if h : ∃ k : ℤ, pentagonal k = n then pentSign h.choose else 0

/-- **The pentagonal number theorem, conditional on Franklin's involution.**

Given `hFranklin` — the single missing combinatorial fact that the signed distinct-partition
count equals `pentCoeff` — the `n`-th coefficient of `genFun pstChar` (i.e. of the pentagonal
product `∏(1 − xⁱ)`) equals `pentCoeff n`, the coefficient of `∑_{k}(−1)ᵏ x^{g_k}`.

This is NOT the unconditional theorem: `hFranklin` is a genuine, currently-unproved hypothesis
(see the module header for the precise obstruction). The proof here supplies everything EXCEPT
that involution. -/
theorem pentagonalNumberTheorem_of_franklin
    (hFranklin : ∀ m : ℕ,
      (∑ p ∈ distincts m, (-1 : ℤ) ^ (Multiset.card p.parts)) = pentCoeff m)
    (n : ℕ) : (genFun pstChar).coeff n = pentCoeff n := by
  rw [coeff_genFun_pstChar]
  exact hFranklin n

open scoped PowerSeries.WithPiTopology in
/-- The conditional pentagonal number theorem, phrased directly on Euler's product
`∏'ᵢ (1 − Xⁱ⁺¹) = ∏_{n≥1}(1 − xⁿ)` via the product identity. Same status: conditional on
`hFranklin`. -/
theorem pentagonalProduct_coeff_of_franklin
    (hFranklin : ∀ m : ℕ,
      (∑ p ∈ distincts m, (-1 : ℤ) ^ (Multiset.card p.parts)) = pentCoeff m)
    (n : ℕ) :
    (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff n = pentCoeff n := by
  rw [← genFun_pstChar_eq_prod]
  exact pentagonalNumberTheorem_of_franklin hFranklin n

end Brockian.PentagonalTheoremFranklin

/-
  Brockian/FranklinInvolution.lean — FRANKLIN'S SIGN-REVERSING INVOLUTION,
  the combinatorial core of the pentagonal number theorem (Aug 2).

  `Brockian/PentagonalTheoremFranklin.lean` proved the Euler-PRODUCT side of the
  pentagonal number theorem and reduced the whole theorem to ONE opaque hypothesis

      hFranklin : ∀ m, (∑ p ∈ distincts m, (-1)^{#parts p}) = pentCoeff m,

  i.e. "the signed count of distinct partitions of `m` collapses to the pentagonal
  coefficient". That module supplied EVERYTHING except the collapse itself.

  This module does the honest next step. Franklin's classical proof of the collapse
  has exactly two ingredients:

    (F1)  a SIGN-REVERSING INVOLUTION on the distinct partitions that are NOT
          fixed points — it flips `#parts` by one, so its contributions cancel in
          pairs; and
    (F2)  the FIXED POINTS are precisely two "staircase" families, whose signed
          count is `pentCoeff m`.

  Ingredient (F1)'s CONSEQUENCE — that a sign-reversing involution off a fixed set
  makes the signed sum equal the sum over the fixed set — is a genuine theorem, and
  we PROVE it here (`signedSum_eq_fixed_of_involution`) from Mathlib's
  `Finset.sum_involution`. This discharges the *summation* heart of Franklin: the
  reason the non-pentagonal partitions contribute nothing is now a proved lemma, not
  an assumption. We also define and prove the defining properties of the two Franklin
  statistics — the smallest part `sPart` and the top-diagonal length `tDiag` — that
  the involution is built from; these are the `s(p)` and `t(p)` of the classical
  argument.

  What remains genuinely missing at Mathlib 4.32 is the CONSTRUCTION of the map
  itself (erase the smallest part / grow the top diagonal, or the reverse) as an
  operation on `Nat.Partition`, together with (F2). We package that irreducible
  remainder as the structure `FranklinData m` and PROVE that `hFranklin` — hence the
  full pentagonal number theorem — follows from `∀ m, FranklinData m`. So this module
  strictly SHRINKS the obstruction: from the monolithic signed-count identity down to
  the explicit involution-with-fixed-sum data, with the cancellation step proved.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `signOf`                       — the weight `(−1)^{#parts p}` of a partition `p`.
  * `signOf_ne_zero`               — `signOf p ≠ 0` (it is always `±1`).
  * `sPart`, `sPart_mem`, `sPart_le`
                                   — Franklin's statistic `s(p)` = smallest part, with
                                     PROOFS that it is an actual part and is minimal.
  * `largestPart`, `largestPart_mem`, `le_largestPart`
                                   — the largest part, an actual part and maximal.
  * `tDiag`, `tDiag_notMem`, `mem_of_lt_tDiag`, `one_le_tDiag`
                                   — Franklin's statistic `t(p)` = length of the top
                                     boundary diagonal, defined as the first gap below
                                     the largest part, with PROOFS that the run
                                     `largest, largest−1, …, largest−(t−1)` is present,
                                     that `largest − t` is absent, and that `t ≥ 1` for
                                     a nonempty partition.
  * `signedSum_eq_fixed_of_involution`
                                   — **the cancellation engine.** A sign-reversing
                                     involution on `distincts m ∖ F` forces
                                     `∑_{distincts m} signOf = ∑_{F} signOf`. Proved via
                                     `Finset.sum_involution`. This is ingredient (F1).
  * `FranklinData`                 — the isolated remaining data: fixed set `F ⊆ distincts m`,
                                     the involution on the complement (membership,
                                     sign-flip, non-fixedness, involutivity), and the
                                     fixed-sum identity `∑_F signOf = pentCoeff m`.
  * `signedSum_eq_pentCoeff_of_franklinData`
                                   — from `FranklinData m`, the signed count equals `pentCoeff m`.
  * `franklin_of_franklinData`     — the same in the exact shape of `hFranklin`.
  * `pentagonalNumberTheorem_of_franklinData`
                                   — **PST conditioned on `∀ m, FranklinData m`.** The `n`-th
                                     coefficient of Euler's product `genFun pstChar` equals
                                     `pentCoeff n`, assuming the Franklin data (NOT the opaque
                                     `hFranklin`). This is a strictly sharper hypothesis: the
                                     cancellation is proved; only the map + fixed-sum remain.

  ## What is NOT proved  (the residual obstruction, now sharpened)
  * `∀ m, FranklinData m` — the CONSTRUCTION of Franklin's map as an operation on
    `Nat.Partition` (case `sPart p ≤ tDiag p`: delete the smallest part and lengthen
    the top diagonal; case `sPart p > tDiag p`: the reverse), the proof that it is a
    sign-reversing involution off the two pentagonal staircase families, and the
    fixed-sum identity `∑_{F} signOf = pentCoeff m`. None of this map machinery exists
    in Mathlib 4.32, and constructing it on `Multiset`-backed partitions is a
    substantial development. We do NOT assert it; we require it as `FranklinData`.

  ## Precise remaining obstruction (exact missing Mathlib combinatorics)
  Everything about how a sign-reversing involution kills the signed sum is now proved
  (`signedSum_eq_fixed_of_involution`), and the two statistics `s = sPart`,
  `t = tDiag` from which the map is defined are constructed with their defining
  properties. The single missing object is a term of type

      ∀ m : ℕ, FranklinData m

  i.e. for each `m` an explicit `Nat.Partition`-valued map `φ` on the non-pentagonal
  distinct partitions of `m` satisfying `signOf (φ p) = − signOf p`, `φ p ≠ p`,
  `φ (φ p) = p`, staying inside the non-fixed set, together with the identification of
  the fixed set `F` as the pentagonal staircases and the count `∑_{F} signOf = pentCoeff m`.
  Building `φ` requires `Multiset` surgery (erase smallest part; add one to the top
  `sPart p` parts / peel the `tDiag p` diagonal into a new smallest part) with the
  attendant positivity, sum-preservation, and `Nodup` proofs — beyond a single module.
-/

set_option autoImplicit false

namespace Brockian.FranklinInvolution

open Nat.Partition Finset
open Brockian.PentagonalTheoremFranklin

/-- The Franklin/Euler weight of a partition: `(−1)` raised to the number of parts.
The signed distinct-partition count is `∑ p ∈ distincts m, signOf p`. -/
def signOf {m : ℕ} (p : m.Partition) : ℤ := (-1 : ℤ) ^ (Multiset.card p.parts)

/-- The weight is never zero (it is always `±1`); this is what lets a sign-reversing
involution pair partitions off with cancelling contributions. -/
theorem signOf_ne_zero {m : ℕ} (p : m.Partition) : signOf p ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-! ### Franklin's statistic `s(p)` — the smallest part -/

open Classical in
/-- Franklin's statistic `s(p)`: the smallest part of `p` (`0` for the empty partition).
Together with `tDiag` this is the pair of statistics from which Franklin's map is built:
the case split is on `sPart p ≤ tDiag p` versus `sPart p > tDiag p`. -/
noncomputable def sPart {m : ℕ} (p : m.Partition) : ℕ :=
  if h : p.parts.toFinset.Nonempty then p.parts.toFinset.min' h else 0

/-- For a nonempty partition, `sPart p` really is one of the parts. -/
theorem sPart_mem {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) : sPart p ∈ p.parts := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [sPart, dif_pos hne, ← Multiset.mem_toFinset]
  exact p.parts.toFinset.min'_mem hne

/-- `sPart p` is `≤` every part: it is the minimum. -/
theorem sPart_le {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) {x : ℕ} (hx : x ∈ p.parts) :
    sPart p ≤ x := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [sPart, dif_pos hne]
  exact Finset.min'_le _ x (Multiset.mem_toFinset.mpr hx)

/-! ### The largest part -/

open Classical in
/-- The largest part of `p` (`0` for the empty partition). The top diagonal `tDiag`
descends from this value. -/
noncomputable def largestPart {m : ℕ} (p : m.Partition) : ℕ :=
  if h : p.parts.toFinset.Nonempty then p.parts.toFinset.max' h else 0

/-- For a nonempty partition, `largestPart p` really is one of the parts. -/
theorem largestPart_mem {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) :
    largestPart p ∈ p.parts := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [largestPart, dif_pos hne, ← Multiset.mem_toFinset]
  exact p.parts.toFinset.max'_mem hne

/-- `largestPart p` is `≥` every part: it is the maximum. -/
theorem le_largestPart {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) {x : ℕ} (hx : x ∈ p.parts) :
    x ≤ largestPart p := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [largestPart, dif_pos hne]
  exact Finset.le_max' _ x (Multiset.mem_toFinset.mpr hx)

/-! ### Franklin's statistic `t(p)` — the top boundary diagonal -/

/-- There is always a gap below the largest part: at `j = largestPart p + 1` the value
`largestPart p − j` is `0`, which is never a part (parts are positive). This existence
underwrites the `Nat.find` definition of `tDiag`. -/
theorem tDiag_gap_exists {m : ℕ} (p : m.Partition) :
    ∃ j, largestPart p - j ∉ p.parts := by
  refine ⟨largestPart p + 1, ?_⟩
  have h0 : largestPart p - (largestPart p + 1) = 0 := by omega
  rw [h0]
  exact fun h => Nat.lt_irrefl 0 (p.parts_pos h)

open Classical in
/-- Franklin's statistic `t(p)`: the length of the top boundary diagonal, i.e. the number
of consecutive values `largestPart p, largestPart p − 1, …` that are all parts, defined as
the first `j` at which `largestPart p − j` fails to be a part. On a distinct partition this
is exactly the length of the rightmost diagonal of the Young diagram. -/
noncomputable def tDiag {m : ℕ} (p : m.Partition) : ℕ := Nat.find (tDiag_gap_exists p)

/-- The value just past the top diagonal is absent: `largestPart p − tDiag p` is not a part. -/
theorem tDiag_notMem {m : ℕ} (p : m.Partition) : largestPart p - tDiag p ∉ p.parts :=
  Nat.find_spec (tDiag_gap_exists p)

/-- Every value inside the top diagonal is present: for `i < tDiag p`, `largestPart p − i`
is a part. This is the defining "unbroken run" property of the diagonal. -/
theorem mem_of_lt_tDiag {m : ℕ} (p : m.Partition) {i : ℕ} (hi : i < tDiag p) :
    largestPart p - i ∈ p.parts :=
  not_not.mp (Nat.find_min (tDiag_gap_exists p) hi)

/-- A nonempty partition has a top diagonal of length at least one (the largest part
itself starts the diagonal). -/
theorem one_le_tDiag {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) : 1 ≤ tDiag p := by
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have hnm : largestPart p - tDiag p ∉ p.parts := tDiag_notMem p
  rw [h, Nat.sub_zero] at hnm
  exact hnm (largestPart_mem hp)

/-! ### The cancellation engine (ingredient F1) -/

/-- **Franklin's cancellation, proved.** Suppose `F ⊆ distincts m` and there is a map `g`
on the *non-fixed* distinct partitions `distincts m ∖ F` that: stays inside `distincts m ∖ F`
(`g_mem`), reverses the sign (`g_sign`), has no fixed point (`g_ne`), and is involutive
(`g_inv`). Then the contributions off `F` cancel in pairs, so

    ∑_{p ∈ distincts m} signOf p = ∑_{p ∈ F} signOf p.

This is exactly why, in Franklin's proof, only the fixed (pentagonal) partitions survive.
The proof is `Finset.sum_involution` on the complement plus the split
`∑_{distincts m} = ∑_{distincts m ∖ F} + ∑_{F}`. -/
theorem signedSum_eq_fixed_of_involution {m : ℕ}
    (F : Finset m.Partition) (hF : F ⊆ distincts m)
    (g : ∀ p ∈ distincts m \ F, m.Partition)
    (g_mem : ∀ p (hp : p ∈ distincts m \ F), g p hp ∈ distincts m \ F)
    (g_sign : ∀ p (hp : p ∈ distincts m \ F), signOf (g p hp) = - signOf p)
    (g_ne : ∀ p (hp : p ∈ distincts m \ F), g p hp ≠ p)
    (g_inv : ∀ p (hp : p ∈ distincts m \ F), g (g p hp) (g_mem p hp) = p) :
    ∑ p ∈ distincts m, signOf p = ∑ p ∈ F, signOf p := by
  have hzero : ∑ p ∈ distincts m \ F, signOf p = 0 := by
    refine Finset.sum_involution g ?_ ?_ g_mem g_inv
    · intro a ha
      rw [g_sign a ha]; ring
    · intro a ha _
      exact g_ne a ha
  have hsplit := Finset.sum_sdiff (f := fun p => signOf p) hF
  rw [hzero, zero_add] at hsplit
  exact hsplit.symm

/-! ### The isolated remaining obstruction, and PST modulo it -/

/-- **The residual combinatorial data Mathlib lacks.** A term of `FranklinData m` is exactly
Franklin's involution package at level `m`: the fixed set `fixed` (the pentagonal staircases),
the sign-reversing involution `map` on the non-fixed distinct partitions, and the fixed-point
sign count. This is what remains unproven; `signedSum_eq_fixed_of_involution` already proves the
consequence that only `fixed` contributes. -/
structure FranklinData (m : ℕ) where
  /-- The fixed points of Franklin's map (the two pentagonal staircase families). -/
  fixed : Finset m.Partition
  /-- Fixed points are distinct partitions. -/
  fixed_subset : fixed ⊆ distincts m
  /-- Franklin's map on the non-fixed distinct partitions. -/
  map : ∀ p ∈ distincts m \ fixed, m.Partition
  /-- The map stays among non-fixed distinct partitions. -/
  map_mem : ∀ p (hp : p ∈ distincts m \ fixed), map p hp ∈ distincts m \ fixed
  /-- The map flips the parity of the number of parts (sign reversal). -/
  map_sign : ∀ p (hp : p ∈ distincts m \ fixed), signOf (map p hp) = - signOf p
  /-- The map has no fixed point off `fixed`. -/
  map_ne : ∀ p (hp : p ∈ distincts m \ fixed), map p hp ≠ p
  /-- The map is an involution. -/
  map_involutive : ∀ p (hp : p ∈ distincts m \ fixed), map (map p hp) (map_mem p hp) = p
  /-- The surviving fixed points carry the pentagonal signed count. -/
  fixed_sum : ∑ p ∈ fixed, signOf p = pentCoeff m

/-- Given Franklin's data at `m`, the signed distinct-partition count is `pentCoeff m`. -/
theorem signedSum_eq_pentCoeff_of_franklinData {m : ℕ} (d : FranklinData m) :
    ∑ p ∈ distincts m, signOf p = pentCoeff m := by
  rw [signedSum_eq_fixed_of_involution d.fixed d.fixed_subset d.map d.map_mem d.map_sign
    d.map_ne d.map_involutive]
  exact d.fixed_sum

/-- Franklin's identity `hFranklin`, in its exact original shape, follows from the Franklin data
for every `m`. This is what `PentagonalTheoremFranklin` took as an unproved hypothesis. -/
theorem franklin_of_franklinData (h : ∀ m, FranklinData m) (m : ℕ) :
    (∑ p ∈ distincts m, (-1 : ℤ) ^ (Multiset.card p.parts)) = pentCoeff m := by
  have hm := signedSum_eq_pentCoeff_of_franklinData (h m)
  simpa only [signOf] using hm

/-- **The pentagonal number theorem, conditioned on `∀ m, FranklinData m`.** The `n`-th
coefficient of Euler's product `genFun pstChar = ∏_{i≥1}(1 − xⁱ)` equals `pentCoeff n`, assuming
Franklin's involution-with-fixed-sum data at every level. This is strictly sharper than the
original `..._of_franklin`: the summation/cancellation step is now proved
(`signedSum_eq_fixed_of_involution`); only the construction of the map and the fixed-sum remain. -/
theorem pentagonalNumberTheorem_of_franklinData (h : ∀ m, FranklinData m) (n : ℕ) :
    (genFun pstChar).coeff n = pentCoeff n :=
  pentagonalNumberTheorem_of_franklin (franklin_of_franklinData h) n

end Brockian.FranklinInvolution
/-
  Brockian/FranklinInvolutionProof.lean — DISCHARGING FRANKLIN'S FIXED POINTS,
  and isolating the involution map (Aug 2).

  `Brockian/FranklinInvolution.lean` proved Franklin's CANCELLATION ENGINE
  (`signedSum_eq_fixed_of_involution`) and reduced the whole pentagonal number
  theorem to a term of the structure `FranklinData m`. That structure has two
  logically separate ingredients, mirroring Franklin's classical proof:

    (F1) the sign-reversing INVOLUTION `map` on the non-fixed distinct partitions
         (its four properties: `map_mem`, `map_sign`, `map_ne`, `map_involutive`);
    (F2) the FIXED SET `fixed` — the two pentagonal staircases — together with the
         identity `∑_{fixed} signOf = pentCoeff m`.

  THIS MODULE PROVES (F2) OUTRIGHT and pins (F1) down to a single named object.

  Concretely: for each integer index `k` we construct the Franklin staircase
  `stair k` — the multiset of parts of the fixed-point partition at index `k`:

      k > 0 :  {k, k+1, …, 2k−1}   (k parts, sum g_k          = pentagonal k)
      k < 0 :  {r+1, …, 2r}        (r = −k parts, sum g_{−r} = pentagonal k)
      k = 0 :  {}                   (empty, sum 0              = pentagonal 0)

  We prove it has `k.natAbs` parts, is `Nodup` (distinct), is positive, and — the
  arithmetic heart — SUMS TO `pentagonal k` (the generalized pentagonal number
  `g_k = k(3k−1)/2`). From this we build the fixed set `fixedPart m` (the single
  staircase realizing `m` when `m` is pentagonal, else `∅`) and PROVE the two
  remaining `FranklinData` fixed-set fields honestly:

    * `fixedPart_subset : fixedPart m ⊆ distincts m`   (they are distinct partitions)
    * `fixedPart_sum    : ∑_{fixedPart m} signOf = pentCoeff m`
        (the surviving staircase carries exactly the pentagonal coefficient `(−1)ᵏ`,
         proved via `(-1)^{k.natAbs} = pentSign k` — the sign identity `neg_one_pow_natAbs`).

  We also prove the SUM-PRESERVATION of Franklin's two elementary moves as pure
  `Multiset` lemmas (`franklin_sum_invariant_down/up`): removing the smallest part
  and lengthening the top diagonal (remove two values `a`,`b`, add `a+b`), and its
  reverse (remove `a`, add `b`,`c` with `b+c=a`), BOTH preserve the partitioned
  integer `m`. These are exactly why Franklin's map lands back inside `Nat.Partition m`.

  We then package the still-missing ingredient (F1) as `FranklinMap m` — the
  involution on `distincts m \ fixedPart m` with its four properties FOR THE
  CONSTRUCTED FIXED SET — and prove `franklinData_of_franklinMap`: an `m`-level
  `FranklinMap` yields a full `FranklinData m` (reusing the proved F2 fields).
  Hence `∀ m, FranklinMap m` ⟹ the UNCONDITIONAL pentagonal number theorem
  (`pentagonalNumberTheorem_of_franklinMap`).

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `gauss_int`                  — `2·∑_{i<c} i = c(c−1)` over ℤ (division-free Gauss sum).
  * `stairBase`, `stair`         — the Franklin staircase multiset at integer index `k`.
  * `stair_card`                 — `|stair k| = k.natAbs` (the staircase has `|k|` parts).
  * `stair_nodup`                — the staircase parts are distinct.
  * `stair_pos`                  — every staircase part is positive.
  * `stair_sum`                  — **`(stair k).sum = pentagonal k`**: the staircase sums to
                                   the generalized pentagonal number `g_k` (the F2 arithmetic).
  * `stairPartAt`                — the staircase as an honest `Nat.Partition m` (when
                                   `pentagonal k = m`).
  * `neg_one_pow_natAbs`         — `(-1)^{k.natAbs} = pentSign k`: the staircase's sign is `(−1)ᵏ`.
  * `fixedPart`                  — Franklin's fixed set at `m` (the realizing staircase, or `∅`).
  * `fixedPart_subset`           — **F2, part 1:** the fixed set consists of distinct partitions.
  * `fixedPart_sum`              — **F2, part 2:** `∑_{fixedPart m} signOf = pentCoeff m`.
  * `franklin_sum_invariant_down/up`
                                 — **F1 arithmetic:** Franklin's two elementary moves preserve
                                   the partitioned integer (sum-preservation), so the map stays
                                   inside `Nat.Partition m`.
  * `FranklinMap`                — the isolated remaining ingredient (F1): the sign-reversing
                                   involution on `distincts m \ fixedPart m`.
  * `franklinData_of_franklinMap`— **the reduction:** a `FranklinMap m` completes the proved F2
                                   fields into a full `FranklinData m`.
  * `pentagonalNumberTheorem_of_franklinMap`
                                 — `∀ m, FranklinMap m` ⟹ the pentagonal number theorem
                                   (coefficient of Euler's product = `pentCoeff n`), UNCONDITIONALLY.

  ## What is NOT proved  (the residual obstruction, now down to F1 alone)
  * `∀ m, FranklinMap m` — the CONSTRUCTION of Franklin's sign-reversing involution `φ` on the
    non-fixed distinct partitions. The two staircase fixed points (F2) and the sum-preservation
    of the elementary moves (F1 arithmetic) are now proved; what remains is to define `φ` by the
    case split `sPart p ≤ tDiag p` vs `sPart p > tDiag p` (using the moves above), and to prove
    it MAPS non-fixed → non-fixed (`map_mem`, including that its only fixed points are the F2
    staircases), FLIPS the sign (`map_sign`), has NO fixed point off `fixedPart m` (`map_ne`),
    and is INVOLUTIVE (`map_involutive`). We do NOT assert `franklinData_exists`
    (`∀ m, FranklinData m`); we require `∀ m, FranklinMap m`.

  ## Precise remaining obstruction (exact missing Mathlib combinatorics)
  A term of `∀ m, FranklinMap m`. Everything about the FIXED points is proved: the staircases
  are constructed, shown distinct, positive, summing to `g_k`, and carrying signed count
  `pentCoeff m` (`fixedPart_sum`); and the elementary moves are shown sum-preserving. What is
  missing is the *global well-definedness and involutivity* of the map `φ`: that the
  `Multiset`-surgery moves preserve `Nodup` (distinctness) in every non-fixed case, that the
  case split is exhaustive off the two staircases, and that `φ ∘ φ = id`. This is the
  `Nodup`/case-analysis core of Franklin's bijection, still absent from Mathlib 4.32 and a
  development beyond one module. It is a single object: the involution `φ`.
-/

set_option autoImplicit false

namespace Brockian.FranklinInvolutionProof

open Nat.Partition Finset
open Brockian.FranklinInvolution
open Brockian.PentagonalTheoremFranklin

/-! ### A division-free Gauss sum -/

/-- `2 · ∑_{i<c} i = c(c−1)` over ℤ, proved by induction (no natural-number subtraction, so it
casts cleanly into the pentagonal identity below). -/
theorem gauss_int (c : ℕ) : 2 * (∑ i ∈ Finset.range c, (i : ℤ)) = (c : ℤ) * ((c : ℤ) - 1) := by
  induction c with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-! ### Franklin's fixed-point staircase -/

/-- The smallest part of the Franklin staircase at index `k`: `k` itself when `k > 0`, and
`|k|+1` when `k ≤ 0` (so `k = 0` gives an empty staircase and `k < 0` starts one higher). -/
def stairBase (k : ℤ) : ℕ := if 0 < k then k.natAbs else k.natAbs + 1

/-- Franklin's fixed-point staircase at integer index `k`: the multiset of `k.natAbs` consecutive
parts starting at `stairBase k`. For `k > 0` this is `{k, …, 2k−1}`; for `k < 0`, `{−k+1, …, −2k}`;
for `k = 0`, empty. This is the parts multiset of the pentagonal fixed point of Franklin's map. -/
def stair (k : ℤ) : Multiset ℕ := (Multiset.range k.natAbs).map (fun i => stairBase k + i)

/-- The staircase has exactly `|k|` parts. -/
theorem stair_card (k : ℤ) : Multiset.card (stair k) = k.natAbs := by
  rw [stair, Multiset.card_map, Multiset.card_range]

/-- The staircase parts are pairwise distinct. -/
theorem stair_nodup (k : ℤ) : (stair k).Nodup := by
  rw [stair]
  exact (Multiset.nodup_range k.natAbs).map (fun a b h => by omega)

/-- Every staircase part is positive. -/
theorem stair_pos {k : ℤ} {x : ℕ} (hx : x ∈ stair k) : 0 < x := by
  rw [stair, Multiset.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Multiset.mem_range] at hi
  have hk : k ≠ 0 := by rintro rfl; simp at hi
  have hb : 1 ≤ stairBase k := by unfold stairBase; split <;> omega
  omega

/-- The staircase written as an explicit `Finset.range` sum (for the sum computation). -/
theorem stair_sum_eq (k : ℤ) :
    (stair k).sum = ∑ i ∈ Finset.range k.natAbs, (stairBase k + i) := rfl

/-- **The F2 arithmetic heart.** The Franklin staircase at index `k` sums to the generalized
pentagonal number `g_k = k(3k−1)/2 = pentagonal k`. This is why the fixed points sit exactly at
the pentagonal exponents. -/
theorem stair_sum (k : ℤ) : (stair k).sum = pentagonal k := by
  -- Closed form of the staircase sum in ℕ (base·count + Gauss triangle), no cast ambiguity.
  have hnat : (stair k).sum = k.natAbs * stairBase k + ∑ i ∈ Finset.range k.natAbs, i := by
    rw [stair_sum_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- The doubled sum equals k(3k−1) over ℤ, by casework on the sign of k.
  have h2 : 2 * ((stair k).sum : ℤ) = k * (3 * k - 1) := by
    rw [hnat, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, mul_add, gauss_int]
    rcases lt_trichotomy k 0 with hk | hk | hk
    · -- k < 0
      have hc : (k.natAbs : ℤ) = -k := by rw [Int.natCast_natAbs, abs_of_neg hk]
      have hb : (stairBase k : ℤ) = -k + 1 := by
        rw [stairBase, if_neg (by omega), Nat.cast_add, Nat.cast_one, hc]
      rw [hc, hb]; ring
    · -- k = 0
      subst hk; simp [stairBase]
    · -- k > 0
      have hc : (k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_pos hk]
      have hb : (stairBase k : ℤ) = k := by rw [stairBase, if_pos hk]; exact hc
      rw [hc, hb]; ring
  have h2' : 2 * ((stair k).sum : ℤ) = 2 * (pentagonal k : ℤ) := by
    rw [h2, two_mul_natCast_pentagonal]
  have h3 := mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2'
  exact_mod_cast h3

/-- The Franklin staircase realized as an honest partition of `m`, when `pentagonal k = m`. -/
def stairPartAt (m : ℕ) (k : ℤ) (hk : pentagonal k = m) : m.Partition where
  parts := stair k
  parts_pos := fun {_} hi => stair_pos hi
  parts_sum := by rw [stair_sum]; exact hk

/-- The staircase's Franklin sign is `(−1)ᵏ`: `(-1)^{k.natAbs} = pentSign k`. This matches the
right-hand-side pentagonal coefficient. -/
theorem neg_one_pow_natAbs (k : ℤ) : (-1 : ℤ) ^ k.natAbs = pentSign k := by
  unfold pentSign
  rcases Int.even_or_odd k with he | ho
  · rw [if_pos he, Even.neg_one_pow (Int.natAbs_even.mpr he)]
  · rw [if_neg (Int.not_even_iff_odd.mpr ho), Odd.neg_one_pow (Int.natAbs_odd.mpr ho)]

/-! ### Franklin's fixed set (F2) -/

open Classical in
/-- Franklin's fixed set at `m`: the single realizing staircase when `m` is a generalized
pentagonal number, and `∅` otherwise. These are the partitions Franklin's involution fixes. -/
noncomputable def fixedPart (m : ℕ) : Finset m.Partition :=
  if h : ∃ k : ℤ, pentagonal k = m then {stairPartAt m h.choose h.choose_spec} else ∅

/-- **F2, part 1.** The fixed set consists of distinct partitions: `fixedPart m ⊆ distincts m`. -/
theorem fixedPart_subset (m : ℕ) : fixedPart m ⊆ distincts m := by
  by_cases hh : ∃ k : ℤ, pentagonal k = m
  · simp only [fixedPart, dif_pos hh]
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp only [distincts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact stair_nodup _
  · simp only [fixedPart, dif_neg hh]
    intro p hp
    simp at hp

/-- **F2, part 2.** The surviving fixed points carry exactly the pentagonal signed count:
`∑_{fixedPart m} signOf = pentCoeff m`. -/
theorem fixedPart_sum (m : ℕ) : ∑ p ∈ fixedPart m, signOf p = pentCoeff m := by
  by_cases hh : ∃ k : ℤ, pentagonal k = m
  · simp only [fixedPart, pentCoeff, dif_pos hh]
    rw [Finset.sum_singleton]
    show (-1 : ℤ) ^ (Multiset.card (stair hh.choose)) = pentSign hh.choose
    rw [stair_card]
    exact neg_one_pow_natAbs hh.choose
  · simp only [fixedPart, pentCoeff, dif_neg hh, Finset.sum_empty]

/-! ### Sum-preservation of Franklin's elementary moves (F1 arithmetic) -/

/-- **Down move preserves the sum.** Removing two parts `a`, `b` and adding one part `c = a+b`
(Franklin's "delete the smallest part, lengthen the top diagonal") keeps the partitioned integer
fixed. This is why the down-map lands back in `Nat.Partition m`. -/
theorem franklin_sum_invariant_down (s : Multiset ℕ) {a b c : ℕ}
    (ha : a ∈ s) (hb : b ∈ s.erase a) (habc : a + b = c) :
    (((s.erase a).erase b) + {c}).sum = s.sum := by
  have h1 : (s.erase a).sum + a = s.sum := by
    conv_rhs => rw [← Multiset.cons_erase ha]
    rw [Multiset.sum_cons]; omega
  have h2 : ((s.erase a).erase b).sum + b = (s.erase a).sum := by
    conv_rhs => rw [← Multiset.cons_erase hb]
    rw [Multiset.sum_cons]; omega
  rw [Multiset.sum_add, Multiset.sum_singleton]
  omega

/-- **Up move preserves the sum.** Removing one part `a` and adding two parts `b`, `c` with
`b + c = a` (Franklin's "peel the top diagonal into a new smallest part") keeps the partitioned
integer fixed. This is why the up-map lands back in `Nat.Partition m`. -/
theorem franklin_sum_invariant_up (s : Multiset ℕ) {a b c : ℕ}
    (ha : a ∈ s) (habc : b + c = a) :
    ((s.erase a) + (b ::ₘ {c})).sum = s.sum := by
  have h1 : (s.erase a).sum + a = s.sum := by
    conv_rhs => rw [← Multiset.cons_erase ha]
    rw [Multiset.sum_cons]; omega
  rw [Multiset.sum_add, Multiset.sum_cons, Multiset.sum_singleton]
  omega

/-! ### The isolated remaining ingredient (F1), and PST modulo it -/

/-- **The single residual object: Franklin's involution (F1), for the constructed fixed set.**
A term of `FranklinMap m` is exactly the sign-reversing involution on the non-fixed distinct
partitions `distincts m \ fixedPart m` — the one piece `FranklinData` still needs once the fixed
set (F2) is proved. -/
structure FranklinMap (m : ℕ) where
  /-- Franklin's map on the non-fixed distinct partitions. -/
  map : ∀ p ∈ distincts m \ fixedPart m, m.Partition
  /-- The map stays among non-fixed distinct partitions. -/
  map_mem : ∀ p (hp : p ∈ distincts m \ fixedPart m), map p hp ∈ distincts m \ fixedPart m
  /-- The map flips the sign (parity of the number of parts). -/
  map_sign : ∀ p (hp : p ∈ distincts m \ fixedPart m), signOf (map p hp) = - signOf p
  /-- The map has no fixed point off `fixedPart m`. -/
  map_ne : ∀ p (hp : p ∈ distincts m \ fixedPart m), map p hp ≠ p
  /-- The map is an involution. -/
  map_involutive : ∀ p (hp : p ∈ distincts m \ fixedPart m), map (map p hp) (map_mem p hp) = p

/-- **The reduction.** A Franklin involution (F1) at level `m` completes the proved fixed-set
fields (F2) into a full `FranklinData m`. Everything except `hm` — i.e. the whole fixed set and
its signed-count identity — is discharged here. -/
noncomputable def franklinData_of_franklinMap (m : ℕ) (hm : FranklinMap m) : FranklinData m where
  fixed := fixedPart m
  fixed_subset := fixedPart_subset m
  map := hm.map
  map_mem := hm.map_mem
  map_sign := hm.map_sign
  map_ne := hm.map_ne
  map_involutive := hm.map_involutive
  fixed_sum := fixedPart_sum m

/-- **The pentagonal number theorem, conditional only on the involution (F1).** Given Franklin's
involution at every level `m`, the `n`-th coefficient of Euler's product `genFun pstChar` equals
`pentCoeff n`. The cancellation engine and the whole fixed-point side (F2) are proved; the sole
hypothesis is the existence of the sign-reversing involution `∀ m, FranklinMap m`. We do NOT prove
that hypothesis, so this is a strict reduction of `franklinData_exists`, not the unconditional PST. -/
theorem pentagonalNumberTheorem_of_franklinMap (h : ∀ m, FranklinMap m) (n : ℕ) :
    (genFun pstChar).coeff n = pentCoeff n :=
  pentagonalNumberTheorem_of_franklinData (fun m => franklinData_of_franklinMap m (h m)) n

end Brockian.FranklinInvolutionProof

/- ARISTOTLE TARGET — construct Franklin's sign-reversing involution FranklinMap (Nodup-preservation + involutivity). Closes the pentagonal number theorem unconditionally (F2 already proved). -/
theorem franklinMap_exists : ∀ (m : ℕ), Brockian.FranklinInvolutionProof.FranklinMap m := by
  sorry
