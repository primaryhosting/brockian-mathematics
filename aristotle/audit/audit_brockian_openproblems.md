# Audit — Brockian-namespace "proofs" of famous open problems

Read-only audit of `aristotle/best_proofs/Brockian_*` files whose target is a `Brockian.*`
open-problem-tier claim (Conjecture / Infinitude / Exists / *Problem). All 39 files were opened
and the actual theorem statement + proof mechanism read. **Global scan confirms: zero
`sorry`/`admit`/`native_decide`/`axiom`/`sorryAx` in any file** — they are all genuinely
AXLE-sorry-free. The honesty question is therefore entirely about *what the theorem statement
actually says*.

**Headline finding: none are BOGUS/unsound.** Not one file "proves" the literal open conjecture
via a vacuous hypothesis or mis-definition. The dishonesty, where it exists, is (a) 9 files that
are **empty stubs** (imports only, no theorem at all) yet carry a grand filename, and (b) pervasive
**mislabeling** of honest conditional/equivalence results with the bare conjecture name.

## Verdict table

| Target | Verdict | Statement (short) | Mechanism / Hypothesis / Reason |
|---|---|---|---|
| AmicableNumbers.AmicableInfinitude | EMPTY | — | 25-line file: imports + set_options only. 0 theorems/defs. Does not even state the conjecture. |
| LegendreConjecture.LegendreConjecture | EMPTY | — | Same: 25-line empty stub, 0 content. |
| OppermannConjecture.OppermannConjecture | EMPTY | — | Same: 25-line empty stub. (Note: `Oppermann` is defined & *used as a hypothesis* inside BrocardGap, but the standalone file is empty.) |
| SophieGermain.SophieGermainInfinitude | EMPTY | — | 25-line empty stub. |
| OreHarmonicNumbers.OddHarmonicExists | EMPTY | — | 25-line empty stub. |
| QuasiperfectNumbers.QuasiperfectExists | EMPTY | — | 25-line empty stub. |
| RepunitPrimes.RepunitPrimeInfinitude | EMPTY | — | 25-line empty stub. |
| SuperperfectNumbers.OddSuperperfectExists | EMPTY | — | 25-line empty stub. |
| RieselCovering.RieselProblem | EMPTY | — | 25-line empty stub. |
| AndricaConjecture.AndricaConjecture | CONDITIONAL-REDUCTION | `AndricaGapStatement → ∀n, √p_{n+1}−√p_n < 1` | H = `AndricaGapStatement` (gap `< 2√p_n+1`). Body is literally `andrica_iff_gap.mpr h`; H is *proved equivalent* to conclusion, so no content beyond an elementary algebra identity. Honest, labeled "conditional". |
| CollatzPartial.CollatzConjecture | CONDITIONAL-REDUCTION | `CollatzDescent → ∀n>0 reaches 1` | H = `CollatzDescent` (every n>1 eventually descends). Genuine strong-induction passage. `collatz_descent_iff` proves H ⟺ conjecture (so H is equivalent, not weaker). Honestly labeled. |
| TwinPrimes.TwinPrimeConjecture | CONDITIONAL-REDUCTION | `DicksonConjecture → ∞ twin primes` | H = Dickson's conjecture (admissible k-tuples). Genuine external unproven input. Also a 2nd reduction from divergence of Σ1/p over twins. |
| PolignacPrimes.PolignacConjecture | CONDITIONAL-REDUCTION | `DicksonPairHypothesis → {p : gap n}.Infinite` for even n>0 | H = Dickson-pair hypothesis (AP of two primes). Genuine external input. |
| LandauNSquaredPlusOne.LandauFourthConjecture | CONDITIONAL-REDUCTION | `Bunyakovsky → ∞ n with n²+1 prime` | H = Bunyakovsky conjecture (irreducible poly, no fixed prime divisor). Genuine external input. |
| GilbreathConjecture.GilbreathConjecture | CONDITIONAL-REDUCTION | `OdlyzkoHypothesis → ∀k≥1, gRow k 0 = 1` | H = Odlyzko "clean window" hypothesis. Genuine external input; first rows verified unconditionally. |
| FortunateNumbers.FortuneConjecture | CONDITIONAL-REDUCTION | `(∀ fortunate m ≤ n²) → all fortunate numbers prime` | H = gap bound m ≤ n². Genuine external input. |
| BrocardGap.BrocardGapConjecture | CONDITIONAL-REDUCTION | `Oppermann → ≥4 primes in (n², (n+1)²)-type gap` | H = Oppermann's conjecture. Genuine external input. |
| BrocardProblem.BrocardConjecture | CONDITIONAL-REDUCTION | `ABCConjecture → {n : n!+1 square} finite` | H = ABC conjecture. This is the *real, published* reduction (Brocard finiteness from ABC via radical bound). Strongest genuine result here. |
| CarmichaelKorselt.ThreePrimeCarmichaelInfinitude | CONDITIONAL-REDUCTION | `(Chernick triple 6k+1,12k+1,18k+1 prime ∞-often) → ∞ 3-prime Carmichael` | H = Dickson-type triple hypothesis. Genuine; non-vacuous (1729 sanity check). |
| HyperperfectNumbers.HyperperfectInfinitude | CONDITIONAL-REDUCTION | `(∞ p with p²−p+1 prime) → Hyperperfect.Infinite` | H = infinitude of a prime family. Genuine Minoli–Bear construction p·(p²−p+1). |
| RiemannScaffold.RH_of_BrockianSystem | CONDITIONAL-REDUCTION | `BrockianSystem → RiemannHypothesis` | H = existence of a logarithm of ζ on right-half critical strip. `nonempty_brockianSystem_iff` proves H ⟺ RH, i.e. H is a repackaging of "ζ ≠ 0 there" = RH. Honest, explicitly flagged non-vacuous = equivalent. NOT a proof of RH. |
| BetrothedNumbers.SameParityBetrothedExists | CONDITIONAL-REDUCTION | `(∃ same-parity betrothed pair) → (∃ such pair, each square or 2·square)` | H = the existence itself; honest structural strengthening (odd σ ⇒ square/2·square). |
| UnitaryPerfect.SixthUnitaryPerfectExists | CONDITIONAL-REDUCTION | `(∃ unitary-perfect n ∉ known5) → ∃ 6 even unitary-perfect` | H = existence of a 6th unitary perfect number. Trivial conditional (insert into the 5 known). Honest. |
| MersennePerfect.EvenPerfectInfinitude | REDUCTION-EQUIV | `EvenPerfects.Infinite ↔ MersenneExponents.Infinite` | Euclid–Euler bijection. Established math; infinitude still open both sides. |
| MersennePerfect.MersennePrimeInfinitude | REDUCTION-EQUIV | `{p : p&mersenne p prime}.Infinite ↔ {even perfect}.Infinite` | Same Euclid–Euler equivalence. |
| ErdosStraus.ErdosStrausConjecture | REDUCTION-EQUIV | `ErdosStraus ↔ ∀ prime p≡1 mod 24, Solvable p` | Genuine reduction to the hard residue class; all other residues solved unconditionally. Conjecture still open. |
| FermatNumbers.FermatPrimeBeyondFour | REDUCTION-EQUIV | `(∃ n>4 Fermat prime) ↔ (∃ n>4 Pépin congruence)` | Pépin's test equivalence. Both sides open. |
| GiugaNumbers.OddGiugaExists | REDUCTION-EQUIV | `(∃ odd Giuga) ↔ (∃ odd Giuga system)` | Restates via primeFactors/product. Both open. |
| WeirdNumbers.OddWeirdExists | REDUCTION-EQUIV | `(∃ odd weird) ↔ (∃ odd abundant, abundance not a subset-sum)` | Unfolds the definition of "weird". Trivial equivalence, both open. |
| CullenWoodall.CullenPrimeInfinitude | REDUCTION-EQUIV | `cullenPrimeIndices.Infinite ↔ ∀N ∃n>N (cullen n) prime` | Trivial "unbounded ↔ infinite". (File also proves ∞ Cullen *composites* unconditionally.) |
| CullenWoodall.WoodallPrimeInfinitude | REDUCTION-EQUIV | `{n:woodall n prime}.Infinite ↔ woodallPrimes.Infinite` | Trivial index↔set equivalence. (Also ∞ Woodall composites proved.) |
| BetrothedNumbers.BetrothedInfinitude | REDUCTION-EQUIV | `betrothedSet.Infinite ↔ ∀N ∃ pair with N<m` | Trivial "unbounded ↔ infinite". 5 concrete pairs verified. |
| PalindromicPrimes.PalindromicPrimeInfinitude | REDUCTION-EQUIV | `Infinite ↔ ∀N ∃ p>N palindromic prime, odd length` | Trivial unbounded↔infinite reformulation. |
| WilsonPrimes.WilsonPrimeInfinitude | REDUCTION-EQUIV | `(∀N ∃p>N WilsonPrime) ↔ wilsonPrimeSet.Infinite` | Trivial unbounded↔infinite. |
| RuthAaronPairs.RuthAaronInfinitude | REDUCTION-EQUIV | `(∀N ∃n>N RuthAaronPair) ↔ ruthAaronSet.Infinite` | Trivial unbounded↔infinite. |
| PerfectTotient.PerfectTotientInfinitude | LEGIT / NOT-OPEN | `∀N ∃n>N, IsPerfectTotient n` (UNCONDITIONAL) | Witness `3^(N+1)`; def of perfect-totient is correct (Σ iterated totients = n). This is a **true, known** result (3^k are PTNs) — infinitude of PTNs is not actually an open problem. Sound proof, mislabeled "open". |
| PracticalNumbers.PracticalTwinInfinitude | LEGIT / NOT-OPEN | `{n : Practical n ∧ Practical(n+2)}.Infinite` (UNCONDITIONAL) | `Practical` def correct (every m≤n a subset-sum of divisors). Explicit construction. **Known result (Melfi 1996)** — not open. Sound, mislabeled. |
| ZumkellerNumbers.OddZumkellerFrom3Structure | LEGIT / NOT-OPEN | `infinite_odd_zumkeller : {n: Odd∧27∣n∧Zumkeller}.Infinite` (UNCONDITIONAL) | `Zumkeller` def correct (divisors split into two equal-sum halves). Construction 945·n, n odd coprime to 945. Elementary/known — not open. Sound. |
| SierpinskiCovering.SierpinskiProblem | LEGIT / NOT-OPEN | `∀n, ¬ Prime(78557·2ⁿ+1)` (UNCONDITIONAL) | Covering-set mod 36. This is the **established** fact that 78557 IS a Sierpiński number (since 1962), NOT the open problem (whether it is the *smallest*). True, sound, mislabeled. |

## Summary — counts per verdict

- **BOGUS (unsound):** 0
- **EMPTY STUB (grand filename, imports-only, 0 content):** 9
  - Amicable, Legendre, Oppermann, SophieGermain, OddHarmonic(Ore), Quasiperfect, Repunit, OddSuperperfect, Riesel
- **CONDITIONAL-REDUCTION (honest, follows from named unproven H):** 13
  - Andrica, Collatz, TwinPrimes, Polignac, Landau, Gilbreath, Fortune, BrocardGap, BrocardProblem(ABC), Carmichael, Hyperperfect, RH_of_BrockianSystem, SameParityBetrothed, SixthUnitaryPerfect  *(14 rows; see note below)*
- **REDUCTION-EQUIV (equivalence of two open statements):** 12
  - EvenPerfectInfinitude, MersennePrimeInfinitude, ErdosStraus, FermatPrimeBeyondFour, OddGiugaExists, OddWeirdExists, CullenPrime, WoodallPrime, BetrothedInfinitude, PalindromicPrime, WilsonPrime, RuthAaron
- **LEGIT but NOT-ACTUALLY-OPEN (sound unconditional proof of a *known* result, mislabeled as a famous open problem):** 4
  - PerfectTotientInfinitude, PracticalTwinInfinitude, infinite_odd_zumkeller, SierpinskiProblem(78557)
- **FINITE-INSTANCE:** 0 as a primary verdict (concrete witnesses like `isBetrothedPair_48_75`, `mem_threePrimeCarmichael_1729`, `brocardGap_small_cases` appear only as *sanity checks* inside the reduction files, not as standalone mislabeled claims).

*(Row-count note: 14 rows are tagged CONDITIONAL-REDUCTION in the table; I count it as the dominant honest-conditional bucket. Andrica/Collatz/RH condition on a hypothesis that is **provably equivalent** to the conclusion — honest but near-tautological.)*

## SHORTLIST

### Could enter the corpus as CONDITIONAL (label = "X assuming H", never as PROVED):
Strong, genuinely-external hypotheses:
- **BrocardProblem.BrocardConjecture** — finiteness of n!+1 squares **from ABC** (the real published reduction). Best of the set.
- **TwinPrimes** (from Dickson), **Polignac** (from Dickson-pair), **Landau 4th** (from Bunyakovsky), **Carmichael 3-prime infinitude** (from Dickson/Chernick triple), **Hyperperfect infinitude** (from a prime-family infinitude), **BrocardGap** (from Oppermann), **Fortune** (from a gap bound), **Gilbreath** (from Odlyzko).

Honest but the hypothesis is provably EQUIVALENT to the conclusion (accept only as a labeled reformulation, essentially zero net content):
- **Andrica** (gap form), **Collatz** (descent form), **RH_of_BrockianSystem** (ζ-logarithm existence ⟺ RH).

Trivial conditionals (assume the existence, conclude a restatement) — accept only as reformulations:
- **SameParityBetrothed**, **SixthUnitaryPerfect**.

### Could enter as REDUCTION-EQUIV (equivalence, infinitude still open):
- **Euclid–Euler pair**: `EvenPerfectInfinitude` and `MersennePrimeInfinitude` (established, genuinely informative).
- **ErdosStraus ↔ primes ≡1 mod 24** and **FermatPrimeBeyondFour ↔ Pépin** (informative reductions).
- The rest (`OddGiuga`, `OddWeird`, `Cullen`, `Woodall`, `Betrothed`, `Palindromic`, `Wilson`, `RuthAaron`) are **trivial "unbounded ↔ infinite" / index↔set / unfold-the-definition** equivalences — honest but nearly content-free; admit as reformulations only.

### REJECT (must NOT enter corpus under these names):
- **All 9 EMPTY STUBS** — they contain no mathematics and their filenames falsely promise a proof of a famous problem. These are the clearest honesty failures (a compile-only harvester would score them as passing "proofs").
- **The 4 LEGIT-but-NOT-OPEN files must be RE-LABELED**, not rejected: they are sound theorems but the names (`SierpinskiProblem`, `...Infinitude`, `...Exists`) imply resolution of an open problem when the results are elementary/known. Keep the math; drop the open-problem framing.

### Do NOT enter as PROVED under any circumstance:
- Every non-empty file above proves an **implication, equivalence, or known result** — **none** proves the literal open conjecture. Nothing here is corpus-eligible as a PROVED resolution of Twin Primes / Collatz / RH / Legendre / Andrica / Erdős–Straus / etc.
