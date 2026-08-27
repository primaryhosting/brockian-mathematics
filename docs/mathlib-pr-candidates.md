# Mathlib PR Candidates — Scouting Report

> Date: 2026-08-27 · Branch: `conveyor/2026-08-18` · Corpus: 11,656 PROVED (registry/theorems.json)
> Goal: ONE clean merged Mathlib PR as a credibility anchor. Scouting only — no fork, no PR opened.
>
> Method: candidate clusters pulled from the registry, statements read from source, Mathlib
> presence checked against (a) GitHub code search in `leanprover-community/mathlib4` (master,
> 2026-08-27), (b) Loogle (`loogle.lean-lang.org`) pattern queries, (c) direct reads of the
> relevant Mathlib files. Axiom cleanliness checked in `registry/theorems.json`
> (all shortlisted theorems: axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, AXLE-verified
> @ lean-4.32.2; note registry `lake_build: pending` — ports must re-elaborate against Mathlib master).

---

## Shortlist (ranked)

| # | Candidate | Corpus source | Mathlib absence evidence | Effort | Fit |
|---|-----------|---------------|--------------------------|--------|-----|
| 1 | **Deficient/Abundant closure pair**: proper multiple of a perfect number is abundant; every positive divisor of a deficient number is deficient | `Brockian/AbundantClosure.lean` (`abundant_of_perfect_dvd`, `deficient_of_dvd_deficient`) | **Strong.** Read `Mathlib/NumberTheory/FactorisationProperties.lean` in full: has `Abundant.of_dvd`, non-strict `abundancyIndex_le_of_dvd`, trichotomy — but NO strict perfect→abundant law and NO `Deficient.of_dvd` dual. Loogle `Nat.Perfect, Nat.Abundant` → 4 hits, none matching; `Nat.Deficient, Dvd.dvd` → 0; `Nat.Perfect, Nat.Deficient, Dvd.dvd` → 0. | **S** | Excellent — fills a visible symmetry gap in an existing file, zero new definitions |
| 2 | **σ(n) is odd ↔ n is a square or twice a square** (+ stepping stone: n has an odd number of divisors ↔ n is a square) | `Brockian/ZumkellerStructure.lean` (`sigma_odd_iff_square_or_two_mul_square`, `odd_card_divisors_iff_isSquare`) | **Strong.** Loogle: `Odd (Nat.divisors _).card` → 0; `Odd (ArithmeticFunction.sigma _ _)` → 0; `IsSquare, Finset.card, Nat.divisors` → 0; GitHub `IsSquare card_divisors` → 0. Nearby infrastructure exists (`Nat.card_divisors`, `Nat.sum_divisors_prime_pow`, `Nat.isSquare_iff_even_factorization`) but neither parity theorem is present. | **S–M** | Classic textbook results, definition-free, natural home `Mathlib/NumberTheory/Divisors.lean` |
| 3 | **Gauss's extension of Wilson's theorem to odd prime powers**: ∏ units of ℤ/pᵏ = −1 (+ lemma: square roots of 1 in ℤ/pᵏ are ±1, p odd) | `Brockian/MsWilsonPrimePower.lean` (`wilson_prime_power`, `units_sq_eq_one`, `prod_units_eq_neg_one`) | **Strong.** Read `Mathlib/NumberTheory/Wilson.lean` in full: prime case only (`wilsons_lemma`, converse), file even carries a TODO to improve it. Loogle `\|- ∏ u : ?Mˣ, u = _` → exactly 1 hit: `FiniteField.prod_univ_units_id_eq_neg_one` (fields only, so ZMod p, not pᵏ). `sq_eq_one'' units ZMod` GitHub → 0. | **M** | Named classical theorem, self-contained 100-line file, target `Mathlib/NumberTheory/Wilson.lean` |
| 4 | **Zumkeller numbers mini-theory**: def + prime powers/deficient numbers are never Zumkeller; perfect ⇒ Zumkeller; coprime-multiple closure; 2ᵏ·p criterion; odd Zumkeller ⇒ non-square | `Brockian/ZumkellerStructure.lean` (whole file, 411 lines) | **Strong on absence.** GitHub `Zumkeller` in mathlib4 → **0 hits anywhere**. | **M** | Good but introduces a NEW definition — needs a notability case (OEIS A083207, published literature); more review friction than #1–#3 |
| 5 | **Derangements textbook closed form**: Dₙ = n!·Σₖ (−1)ᵏ/k! over ℚ | `Brockian/MsDerangement.lean` (`derangement_closed`) | **Moderate.** `Mathlib/Combinatorics/Derangements/Finite.lean` has only the ℤ/ascFactorial form `numDerangements_sum`; Loogle `numDerangements` → 9 hits, none over ℚ/division form; `Exponential.lean` even re-derives this shape inline for the e⁻¹ limit. | **S** | Small and clean, but highest "this is just a cast of an existing lemma" rejection risk |

## Eliminated (Mathlib already has it, or poor fit)

| Candidate | Corpus name | Why eliminated |
|-----------|-------------|----------------|
| **Erdős–Ginzburg–Ziv** | `Brockian.ErdosGinzburgZiv.erdos_ginzburg_ziv` | Mathlib HAS it: `ZMod.erdos_ginzburg_ziv` in `Mathlib/Combinatorics/Additive/ErdosGinzburgZiv.lean`. The corpus proof is itself a 5-line corollary of the Mathlib theorem. |
| **Euler odd = distinct partitions** | `Brockian.OddDistinctPartition.euler_odd_eq_distinct` | Mathlib HAS it: `Nat.Partition.card_odds_eq_card_distincts` (`Mathlib/Combinatorics/Enumerative/Partition/Glaisher.lean`). Corpus file is explicitly a "Mathlib wire." |
| **Glaisher's theorem** (general m) | `Brockian.OddDistinctPartition.glaisher` | Mathlib HAS it: `Nat.Partition.card_restricted_eq_card_countRestricted`, same file. Also a wire. |
| **Pentagonal number theorem** | `Brockian.FranklinFixedPoint.pentagonalNumberTheorem` | Mathlib GOT it in 2025 (Weiyi Wang): `Mathlib/Combinatorics/Enumerative/Pentagonal/{Basic,Ring,PowerSeries}.lean` — verified by direct read; proves ∏(1−xⁿ⁺¹) = pentagonal series in R⟦X⟧. The corpus's independent proof postdates its own claim that Mathlib listed PNT as TODO. (Franklin's *combinatorial involution* is still absent from Mathlib, but a duplicate-proof PR is a poor first-PR play; note it as a possible later "alternative proof / bijective machinery" contribution.) |
| **Wilson at ℕ level** | `Brockian.WilsonGeneral.prime_iff_dvd_factorial_succ` | Mathlib effectively has it: 4-line rewrite of the existing `Nat.prime_iff_fac_equiv_neg_one`. Could ride along as a convenience corollary in candidate #3's PR, not carry a PR alone. |
| **Admissibility / prime k-tuples machinery** | `Brockian.Admissibility*` (1,200+ registry entries) | Genuinely absent from Mathlib, but it is a definitional *framework* (LocalTupleAdmissible, localNu, CRT counting scaffold) with Brockian-program-specific shape. Wrong vehicle for "one clean merged PR"; would need an RFC-style discussion first. |

---

## Candidate details

### 1. Abundant/Deficient closure pair — RECOMMENDED FIRST PR

- **Corpus names:** `Brockian.AbundantClosure.abundant_of_perfect_dvd`,
  `Brockian.AbundantClosure.deficient_of_dvd_deficient`
  (registry: PROVED, axioms {propext, Classical.choice, Quot.sound}, AXLE @4.32)
- **Informal statements:**
  - If `a` is perfect, `a ∣ n`, and `a < n`, then `n` is abundant. (Strict — the extra divisor 1
    pushes σ(n) past 2n; Mathlib's `abundancyIndex_le_of_dvd` gives only the non-strict bound.)
  - If `n` is deficient and `d ∣ n`, `d ≥ 1`, then `d` is deficient (downward closure, proved via
    trichotomy + the first law + existing `Abundant.of_dvd`).
- **Target file:** `Mathlib/NumberTheory/FactorisationProperties.lean` (definitions, trichotomy,
  `Abundant.of_dvd`, `abundant_iff_sum_divisors` all already live there — the PR adds ~60 lines
  and no imports).
- **Mathlib-absence evidence:** full read of the target file (decl list enumerated 2026-08-27);
  Loogle queries above all 0.
- **Effort: S.** Proof uses only stable API already imported by the target file
  (`Nat.perfect_iff_sum_divisors_eq_two_mul`, `Finset.sum_image`, `Finset.sum_le_sum_of_subset`,
  `Nat.mem_divisors`, `omega`).
- **Risk notes:** essentially none mathematically. Main review work is naming + docstrings.
  The corpus file's `prime_deficient` and `exists_prime_factor_of_abundant` are already in
  Mathlib (`Nat.Prime.deficient`; trivial) — do NOT port those.

### 2. σ-parity theorems

- **Corpus names:** `Brockian.ZumkellerStructure.sigma_odd_iff_square_or_two_mul_square`,
  `odd_card_divisors_iff_isSquare` (both PROVED, axiom-clean).
- **Informal:** σ(n) odd ↔ (n square ∨ 2n square); #divisors(n) odd ↔ n square.
- **Target:** `Mathlib/NumberTheory/Divisors.lean` (where `Nat.card_divisors`,
  `Nat.sum_divisors_prime_pow` live), or a small new `Divisors/Parity` section.
- **Adaptation:** corpus helper lemmas `isSquare_of_factorization_even` /
  `factorization_even_of_isSquare` collapse into Mathlib's existing
  `Nat.isSquare_iff_even_factorization`; `Finset.odd_sum_iff_odd_card_odd` already exists and is
  what the corpus proof uses. Net port ≈ 80 lines. Effort S–M.
- **Risk:** low; both are classic (Sierpiński exercises). Slight chance a reviewer asks to state
  via `ArithmeticFunction.sigma 1` as well — cheap to add.

### 3. Gauss–Wilson for odd prime powers

- **Corpus names:** `Brockian.MsWilsonPrimePower.wilson_prime_power` (+ `units_sq_eq_one`,
  `prod_units_eq_neg_one`, `prime_pow_dvd_of_dvd_pred_mul_succ`); companion universal fact
  `Brockian.GaussWilson.prod_units_sq_eq_one` ((∏ units of ZMod n)² = 1, any n).
- **Informal:** for odd prime p and k ≥ 1, the product of all units of ℤ/pᵏ is −1
  (Gauss's generalization of Wilson). Stepping stone of independent value: x² = 1 in (ZMod pᵏ)ˣ
  ⇒ x = ±1 for odd p.
- **Target:** `Mathlib/NumberTheory/Wilson.lean` (file has a TODO inviting improvement) or
  `Mathlib/Data/ZMod/Units.lean` for the square-roots lemma.
- **Effort: M.** 102-line self-contained file; reviewers will likely ask to (a) expose
  `units_sq_eq_one` as a public iff lemma, (b) possibly route the pairing argument through a
  general "product of all elements of a finite abelian group = product of the involutions"
  lemma. The 2pᵏ and n=4 cases + the "+1 otherwise" completion (full Gauss statement) are NOT
  in the corpus — the PR should be honest that it covers the odd-prime-power case.
- **Risk:** medium-low. Genuinely wanted; slightly more review surface than #1/#2.

### 4. Zumkeller mini-theory

- **Corpus names:** `Brockian.ZumkellerStructure.*` — def `Zumkeller`, `zumkeller_of_perfect`,
  `not_zumkeller_of_deficient`, `not_zumkeller_of_sigma_odd`, `not_zumkeller_prime_pow`,
  `zumkeller_iff_partition`, `zumkeller_mul_coprime`, `zumkeller_two_pow_mul_prime`,
  `odd_zumkeller_not_square` (all PROVED, axiom-clean). Plus numeric instances in
  `ZumkellerNumbers.lean`.
- **Target:** new file `Mathlib/NumberTheory/Zumkeller.lean` (import `FactorisationProperties`).
- **Effort: M.** Code is clean and general, but: two duplicate `Zumkeller` defs exist in the
  corpus (`ZumkellerNumbers` vs `ZumkellerStructure`) — pick one; the σ-parity lemmas inside
  `ZumkellerStructure.lean` should be split out (they are candidate #2 and belong in Divisors);
  numeric instances (`zumkeller_six` etc.) should mostly be dropped or `decide`d.
- **Risk:** medium — new-definition PRs need a notability argument (OEIS A083207;
  Rao–Peng, *On Zumkeller numbers*, J. Number Theory 2013 — cite in module docstring) and
  invite naming/API debate. Strong SECOND PR once #1 establishes credibility; pairs naturally
  with it (`zumkeller_of_perfect`, `not_zumkeller_of_deficient` consume FactorisationProperties).

### 5. Derangements ℚ closed form

- **Corpus name:** `Brockian.MsDerangement.derangement_closed` (PROVED, axiom-clean, 20 lines).
- **Informal:** (numDerangements n : ℚ) = n!·Σ_{k≤n} (−1)ᵏ/k!.
- **Target:** `Mathlib/Combinatorics/Derangements/Finite.lean` next to `numDerangements_sum`;
  suggested name `numDerangements_eq_factorial_mul_sum` (state for any `Field`/`DivisionRing`
  of characteristic 0 if reviewers ask).
- **Effort: S. Risk: medium** — a reviewer may prefer deriving it from `numDerangements_sum` by
  cast rather than fresh induction (do that: it shortens the proof and raises acceptance odds).
  Bonus: `Exponential.lean` currently reconstructs exactly this expression inline for
  `numDerangements_tendsto_inv_e`; refactoring it to use the new lemma gives the PR a
  "simplifies existing code" selling point.

---

## Recommendation: do #1 first (Abundant/Deficient closure pair)

**Rationale.** It is the only candidate that simultaneously: (a) needs no new definitions,
(b) lands in an actively maintained existing file whose API it visibly completes
(`Abundant.of_dvd` exists; its `Deficient` dual conspicuously does not), (c) is ≤100 lines of
review surface, (d) uses only lemmas already imported by the target file, and (e) has
bulletproof absence evidence from a full read of the target file rather than search heuristics.
It is the archetype of a first-time-contributor PR that gets merged in days. #2 is the natural
follow-up (same reviewer pool), #4 the natural third (cites #1's file).

### Concrete adaptation sketch for #1

1. **Branch off mathlib4 master** (human forks; scouting stops here). Toolchain: whatever
   `mathlib4/lean-toolchain` says (corpus is at 4.32.x — expect only cosmetic drift;
   the proof uses no fragile automation beyond `omega`).
2. **Edit `Mathlib/NumberTheory/FactorisationProperties.lean`**, adding after `Abundant.of_dvd`
   (≈ line 213):
   - ```
     /-- A proper multiple of a perfect number is abundant. -/
     theorem Perfect.abundant_of_dvd_of_lt (ha : n.Perfect) (hdvd : n ∣ m) (hlt : n < m) :
         Abundant m
     ```
     Proof = corpus `abundant_of_perfect_dvd` verbatim modulo: `Nat.` prefixes dropped
     (inside `namespace Nat`), `Finset.` opened, keep the image-of-scaled-divisors argument;
     finish with the file's own `abundant_iff_sum_divisors`.
   - ```
     /-- Every positive divisor of a deficient number is deficient. -/
     theorem Deficient.of_dvd (h : Deficient n) (hdvd : m ∣ n) (hm : m ≠ 0) : Deficient m
     ```
     Proof = corpus `deficient_of_dvd_deficient` with `1 ≤ d` swapped for the Mathlib-idiomatic
     `m ≠ 0`, using the file's `deficient_iff_not_abundant_and_not_perfect`,
     `deficient_or_perfect_or_abundant`, `Abundant.of_dvd`, and the new
     `Perfect.abundant_of_dvd_of_lt`.
   - Optionally `theorem abundant_of_six_dvd` as a `decide`-fed corollary — drop if reviewers
     balk; it mirrors the file's existing taste for small witnesses (`abundant_twelve`).
   - Update the module docstring's "Main Results" list; add the implication note
     "deficiency is closed under divisors; perfect numbers have no perfect proper multiples".
3. **Naming/style pass:** 100-col lines, `⦃⦄`-free explicit binders matching neighbors,
   docstrings on both theorems, no `private` helpers (inline the two `have`-blocks).
4. **Local verification:** `lake exe cache get && lake build Mathlib.NumberTheory.FactorisationProperties`,
   then `lake exe mk_all --check` (no-op, existing file) and run the file through
   `scripts/lint-style` per CONTRIBUTING.md.
5. **PR framing:** title
   `feat(NumberTheory/FactorisationProperties): divisors of deficient numbers are deficient`
   ; body states both laws, notes the strictness gap vs `abundancyIndex_le_of_dvd`, and that
   proofs are elementary (no new imports). Do not mention corpus provenance machinery; the
   mathematics stands alone. Human opens the PR and handles the Mathlib CLA/label flow.

**Expected end-to-end effort:** 2–4 hours including CI round-trips.
