# The Open Frontier — formalized partial progress on unsolved problems

*This is the honest ledger of the frontier lane: machine-verified partial results toward
genuinely open problems, with the open boundary drawn precisely. Every theorem cited here
resolves to a green entry in `registry/theorems.json`; every "OPEN" line is a statement we
do **not** prove. Nothing here claims to solve a famous conjecture — the value is a sharply
drawn, independently AXLE-verified frontier.*

## How to read this

- **PROVED** — an unconditional theorem in the verified core (AXLE @ lean-4.32.0, axioms ⊆
  {propext, Classical.choice, Quot.sound}, no `sorry`/`native_decide`).
- **OPEN** — a precisely-stated claim we deliberately leave unproven; where possible we
  *characterize* the open set rather than gesture at it.
- Registered conjectures live in the CONJECTURE register as unproven `def`s, never theorems.

---

## Erdős–Straus conjecture (open since 1948)

**Claim.** For every integer n ≥ 2, `4/n = 1/x + 1/y + 1/z` in positive integers.
Module: `Brockian.ErdosStraus`, `Brockian.ErdosStrausResidues`.

**PROVED (unconditional):**
- Even n, and n divisible by 3, 5, or 7 — explicit verified Egyptian-fraction identities
  (`erdosStraus_even`, `erdosStraus_dvd_three`, `erdosStraus_dvd_five`, `erdosStraus_dvd_seven`).
- Residue classes n ≡ 3 (mod 4) and n ≡ 2 (mod 3) (`erdosStraus_mod4_three`, `erdosStraus_mod3_two`).
- **Multiplicativity** — solvability is inherited by multiples (`erdosStraus_of_dvd`), hence the
  whole conjecture **reduces to primes** (`erdosStraus_of_prime_case`).
- Consolidated coverage (`erdosStraus_covered`).

**OPEN, characterized sharply.** Any counterexample n must be odd, coprime to 3, and
≡ 1 (mod 4) — i.e. **n ≡ 1 (mod 12)**, equivalently n%24 ∈ {1, 13}
(`erdosStraus_open_reduces`, `erdosStraus_open_reduces_mod12`, `erdosStraus_open_frontier_mod24`).
This pins failure to the classes feeding the hard primes p ≡ 1, 121, 169, 289, 361, 529 (mod 840).
A computational search over many moduli found **no** linear parametric identity closing those
classes — consistent with the known theory that they are genuinely open. The full conjecture
`ErdosStrausConjecture` is recorded as an unproven `def`.

---

## Odd perfect numbers (open ~2000 years)

**Claim.** No odd perfect number exists (existence unknown). A perfect number satisfies σ(n) = 2n.
Module: `Brockian.OddPerfectConstraints`.

**PROVED (necessary conditions — "if one exists, then…"):**
- An odd perfect number is **not a perfect square** (`oddPerfect_not_square`): σ of an odd square is
  odd, but σ(n) = 2n is even.
- An odd perfect number is **not a prime power** (`oddPerfect_not_prime_pow`).
- Sanity: positive, odd, > 1.

**OPEN.** Existence itself; Euler's form n = p^k·m² with p ≡ k ≡ 1 (mod 4) (attempted, not yet
proved — a genuine formalization target for a later cycle).

---

## Lehmer's totient problem (open since 1932)

**Claim.** `φ(n) ∣ (n − 1)` implies n prime. Module: `Brockian.LehmerTotient`.
A "Lehmer number" is a composite n with φ(n) ∣ (n − 1); none are known.

**PROVED (necessary conditions on a hypothetical counterexample):**
- A Lehmer number is **odd** (`lehmer_odd`): φ(n) is even but n − 1 would be odd.
- A Lehmer number is **squarefree** (`lehmer_squarefree`, flagship): p² ∣ n gives p ∣ φ(n) ∣ (n−1)
  while p ∣ n, forcing p ∣ 1.
- A Lehmer number has **≥ 3 distinct prime factors** (`lehmer_three_primes`): the p·q case reduces to
  `ab ∣ (a+b)` with a, b ≥ 2, a ≠ b — impossible.

**OPEN.** Existence of any Lehmer number (equivalently, whether the implication holds).

---

## Collatz (3n+1) conjecture (open)

**Claim.** Every positive integer reaches 1 under n ↦ (n/2 if even, else 3n+1).
Module: `Brockian.CollatzPartial`. `CollatzConjecture` is an unproven `def` (CONJECTURE register).

**PROVED (unconditional partial results):**
- The trivial cycle 1 → 4 → 2 → 1 (`trivial_cycle`).
- **Powers of two reach 1** (`reaches1_pow_two`), via `collatz(2n) = n` (`collatz_two_mul`).
- Descent by halving: `Reaches1 n → Reaches1 (2^k · n)` (`reaches1_two_mul`, `reaches1_mul_pow_two`).
- **Terras-style descent** (`descent_mod4_one`): every n ≡ 1 (mod 4) with n > 1 reaches a value
  strictly below n in 3 steps (12m+4 → 6m+2 → 3m+1 < 4m+1).

**OPEN.** The conjecture itself; the absence of any nontrivial cycle; convergence of a general n.

---

## Sierpiński numbers (problem open since 1960)

**Claim.** Is 78557 the *smallest* Sierpiński number (odd k with k·2ⁿ+1 composite for all n ≥ 1)?
Module: `Brockian.SierpinskiCovering`. `SierpinskiProblem` is an unproven `def`.

**PROVED (a concrete verified membership):**
- **78557 IS a Sierpiński number** (`sierpinski_78557`): for every n ≥ 1, 78557·2ⁿ+1 is composite —
  proved via the covering set {3,5,7,13,19,37,73}. Supporting: `two_pow_periodic`
  (2ⁿ ≡ 2^(n mod 36) mod p, since 2³⁶ ≡ 1 mod each p), `covering_table` (all 36 residues covered,
  by `decide`), `composite_of` (divisibility transfer + primality exclusion).

**OPEN.** Whether 78557 is the *smallest* such k (the remaining candidates below it are unresolved).
This is a concrete verified membership in an open problem's exceptional set — not a resolution.

---

## Riesel numbers (problem open since 1956)

**Claim.** Is 509203 the *smallest* Riesel number (odd k with k·2ⁿ−1 composite for all n ≥ 1)?
Module: `Brockian.RieselCovering`. `RieselProblem` is an unproven `def`.

**PROVED (concrete verified membership):**
- **509203 IS a Riesel number** (`riesel_509203`): for every n ≥ 1, 509203·2ⁿ−1 is composite —
  via the covering set {3,5,7,13,17,241} (modulus 24). Mirror of the Sierpiński proof applied to
  the −1 family: `two_pow_periodic`, `covering_table`, `composite_of`.

**OPEN.** Whether 509203 is the *smallest* such k. A concrete verified membership, not a resolution.

---

## Amicable numbers (infinitude open)

**Claim.** Are there infinitely many amicable pairs (m ≠ n with s(m)=n, s(n)=m, where s is the
aliquot sum)? Module: `Brockian.AmicableNumbers`. `AmicableInfinitude` is an unproven `def`.

**PROVED (concrete verified instances + aliquot dynamics):**
- **(220, 284)** (`amicable_220_284`, Thābit ibn Qurra), **(1184, 1210)** (`amicable_1184_1210`,
  Paganini 1866), **(2620, 2924)** (`amicable_2620_2924`, Euler) — each verified by kernel
  computation of the aliquot sums.
- Aliquot dynamics: a perfect number is a fixed point of the aliquot map
  (`perfect_iff_aliquot_fixed`); amicability is symmetric (`amicable_symm`); an amicable number is
  not perfect (`amicable_not_perfect`) — a genuine 2-cycle is not a fixed point.

**OPEN.** Whether infinitely many amicable pairs exist.

---

## Giuga numbers (odd-Giuga existence open)

**Claim.** Does an *odd* Giuga number exist? (A Giuga number is a composite n > 1 with p ∣ (n/p − 1)
for every prime p ∣ n.) Open — exactly parallel to the odd perfect number problem.
Module: `Brockian.GiugaNumbers`. `OddGiugaExists` is an unproven `def`.

**PROVED:**
- **30 and 858 are Giuga numbers** (`giuga_30`, `giuga_858`) — concrete verified instances.
- **Every Giuga number is squarefree** (`giugaNumber_squarefree`): if p² ∣ n then p ∣ (n/p) and
  p ∣ (n/p − 1), forcing p ∣ 1.

**OPEN.** Whether any odd Giuga number exists.

---

## Carmichael numbers / Korselt's criterion (three-prime infinitude open)

**Claim.** Are there infinitely many Carmichael numbers with *exactly three* prime factors?
(*General* Carmichael infinitude is a **theorem** — Alford–Granville–Pomerance 1994 — not open.)
Module: `Brockian.CarmichaelKorselt`. `ThreePrimeCarmichaelInfinitude` is an unproven `def`.

**PROVED (concrete + structural):**
- **561, 1105, 1729 are Carmichael numbers** (`korselt_561`, `korselt_1105`, `korselt_1729`) via
  Korselt's criterion (squarefree + (p−1)∣(n−1) for all p∣n). 1729 is the Hardy–Ramanujan taxicab.
- **Every Carmichael number is odd** (`korselt_odd`).

**OPEN.** Whether infinitely many Carmichael numbers have exactly three prime factors (a genuine
refinement of a solved problem — the frontier marks only what is actually open).

---

## Brocard's problem / Brown numbers (open)

**Claim.** For which n is n! + 1 a perfect square? Only three solutions are known: (4,5), (5,11),
(7,71); whether others exist is open. Module: `Brockian.BrocardProblem`. `BrocardConjecture`
(only n ∈ {4,5,7}) is an unproven `def`.

**PROVED (concrete + structural + search-narrowing):**
- **The three known Brown pairs** (`brown_4_5`, `brown_5_11`, `brown_7_71`).
- Structural: in any Brown pair m is odd (`brown_m_odd`) and n! = (m−1)(m+1) (`brown_factorization`).
- **No solutions for n = 8, 9, 10** (`no_brown_8_9_10`) — via consecutive-square gaps.

**OPEN.** Whether any Brown pair exists beyond the three known.

---

## Mersenne primes / even perfect numbers (infinitude open)

**Claim.** Are there infinitely many Mersenne primes (equivalently, infinitely many even perfect
numbers)? Open — one of the oldest problems in mathematics. Module: `Brockian.MersennePerfect`.
`MersennePrimeInfinitude` and `EvenPerfectInfinitude` are unproven `def`s.

**PROVED:**
- **6, 28, 496, 8128 are perfect numbers** (`perfect_6/28/496/8128`) and **3, 7, 31, 127 are Mersenne
  primes** (`mersenne_{2,3,5,7}_prime`).
- The Euclid–Euler correspondence, **re-proved from main-library API** (the Mathlib lemmas live only
  in the Archive), both directions.
- **The two open statements are equivalent** (`infinitude_equiv`): infinitely many Mersenne primes ⟺
  infinitely many even perfect numbers.

**OPEN.** Either infinitude (they stand or fall together, but neither is proved).

---

## Twin primes (conjecture open)

**Claim.** Are there infinitely many primes p with p+2 also prime? Open — one of the most famous
problems in mathematics. Module: `Brockian.TwinPrimes`. `TwinPrimeConjecture` is an unproven `def`.

**PROVED (concrete + structural):**
- **Eight twin pairs** (`twin_3`, `twin_5`, `twin_11`, `twin_17`, `twin_29`, `twin_41`, `twin_59`,
  `twin_71`) — (3,5) through (71,73).
- **The middle of any twin pair p ≥ 5 is divisible by 6** (`twin_middle_div_six`): p is odd so
  2 ∣ p+1, and among p, p+1, p+2 exactly one is a multiple of 3 — not the two primes — so 3 ∣ p+1.
- Corollary: every twin pair (p ≥ 5) has the form (6k−1, 6k+1) (`twin_form_6k`).

**OPEN.** Whether infinitely many twin primes exist.

---

## Sophie Germain primes (infinitude open)

**Claim.** Are there infinitely many primes p with 2p+1 also prime? Open.
Module: `Brockian.SophieGermain`. `SophieGermainInfinitude` is an unproven `def`.

**PROVED (concrete + structural):**
- **Eight Sophie Germain primes** (`sg_2`, `sg_3`, `sg_5`, `sg_11`, `sg_23`, `sg_29`, `sg_41`, `sg_53`).
- **A Sophie Germain prime p > 3 satisfies p ≡ 5 (mod 6)** (`sg_mod_six`): if p ≡ 1 (mod 6) then
  3 ∣ (2p+1), forcing the prime 2p+1 = 3, impossible.
- Corollary: the safe prime 2p+1 ≡ 11 (mod 12) (`sg_safe_mod`).

**OPEN.** Whether infinitely many Sophie Germain primes exist.

---

## Polignac's conjecture — cousin & sexy primes (open)

**Claim.** For every even gap k > 0, are there infinitely many prime pairs (p, p+k)?
(Twin = gap 2, cousin = gap 4, sexy = gap 6.) Open. Module: `Brockian.PolignacPrimes`.
`PolignacConjecture` is an unproven `def`.

**PROVED (concrete + structural):**
- **Eight cousin pairs** (gap 4): `cousin_3` … `cousin_79`. **Eight sexy pairs** (gap 6):
  `sexy_5` … `sexy_47`.
- **A cousin prime p > 3 satisfies p ≡ 1 (mod 6)** (`cousin_mod_six`; corollary `cousin_form_6k`:
  the pair is (6k+1, 6k+5)). Sexy primes share a residue mod 6 (`sexy_same_mod_six`).

**OPEN.** Whether any fixed even gap occurs infinitely often (de Polignac).

---

## Fermat numbers (more Fermat primes? open)

**Claim.** Is any Fermat number F_n = 2^(2ⁿ)+1 prime for n ≥ 5? Only F₀…F₄ are known prime;
conjectured none beyond. Module: `Brockian.FermatNumbers`. `FermatPrimeBeyondFour` is an unproven `def`.

**PROVED:**
- **The five known Fermat primes** (`fermat_0_prime`…`fermat_4_prime`): 3, 5, 17, 257, 65537.
- **F₅ and F₆ composite** via explicit factorization (`fermat_5_eq`/`_not_prime` = 641·6700417, Euler
  1732; `fermat_6_eq`/`_not_prime` = 274177·67280421310721).
- **Fermat numbers are pairwise coprime** (`fermat_coprime`, Goldbach's theorem — reused from
  Mathlib's `Nat.fermatNumber` API) — which itself yields the infinitude of primes.

**OPEN.** Whether any Fermat number beyond F₄ is prime.

---

## Landau's fourth problem — primes of the form n²+1 (open)

**Claim.** Are there infinitely many primes of the form n²+1? Open since 1912 (one of the four
problems Landau called "unattackable"). Module: `Brockian.LandauNSquaredPlusOne`.
`LandauFourthConjecture` is an unproven `def`.

**PROVED (concrete + structural):**
- **Ten n²+1 primes** (`nsq_1`, `nsq_2`, `nsq_4`, …, `nsq_26`): witnesses 2, 5, 17, 37, 101, 197,
  257, 401, 577, 677.
- **For n > 1, if n²+1 is prime then n is even** (`nsq_even_of_prime`): n odd ⇒ n²+1 even and > 2 ⇒
  not prime. Corollary `nsq_mod_two_of_prime`.

**OPEN.** Whether infinitely many primes of the form n²+1 exist.

---

## Cullen & Woodall numbers (prime infinitude open)

**Claim.** Are there infinitely many Cullen primes (C_n = n·2ⁿ+1)? Woodall primes (W_n = n·2ⁿ−1)?
Both open. Module: `Brockian.CullenWoodall`. `CullenPrimeInfinitude` / `WoodallPrimeInfinitude`
are unproven `def`s.

**PROVED (concrete + structural):**
- **Primes:** C₁ = 3 (`cullen_1_prime`); W₂ = 7, W₃ = 23, W₆ = 383 (`woodall_2/3/6_prime`).
- **Composites:** C₂ = 9, C₃ = 25, W₄ = 63, W₅ = 159 (`cullen_2/3_not_prime`, `woodall_4/5_not_prime`).
- Structural: C_n = W_n + 2 (`cullen_sub_woodall`); both are odd for n ≥ 1 (`cullen_odd`, `woodall_odd`).

**OPEN.** Whether infinitely many Cullen (resp. Woodall) primes exist.

---

## Repunit primes (infinitude open)

**Claim.** Are there infinitely many repunit primes R_n = (10ⁿ−1)/9 = 11…1?
Open. Module: `Brockian.RepunitPrimes`. `RepunitPrimeInfinitude` is an unproven `def`.

**PROVED (concrete + structural):**
- **R₂ = 11 is prime** (`repunit_2_prime`); R₁, R₃, R₄, R₅, R₆ composite.
- **d ∣ n ⇒ R_d ∣ R_n** (`repunit_dvd_of_dvd`), and hence **R_n prime ⇒ n prime**
  (`prime_of_repunit_prime`) — the base-10 analog of the Mersenne exponent constraint.
- Repunits are strictly increasing (`repunit_strictMono`).

**OPEN.** Whether infinitely many repunit primes exist.

---

## Legendre's conjecture — Landau's third problem (open)

**Claim.** Is there always a prime between consecutive squares, n² < p < (n+1)²? Open.
Module: `Brockian.LegendreConjecture`. `LegendreConjecture` is an unproven `def`.

**PROVED:**
- **Twelve concrete witnesses** (`legendre_1`…`legendre_12`): a prime between n² and (n+1)² for
  n = 1…12 (e.g. 144 < 149 < 169).
- **Bertrand's postulate** (`bertrand_holds`, reused from Mathlib): a prime in (n, 2n] — the *proven*
  weaker window that Legendre would strengthen to (n², (n+1)²).

**OPEN.** Whether a prime lies between every pair of consecutive squares.

---

## Andrica's conjecture — prime gaps (open)

**Claim.** For consecutive primes, √pₙ₊₁ − √pₙ < 1? Open. Module: `Brockian.AndricaConjecture`.
`AndricaConjecture` is an unproven `def`.

**PROVED (concrete + bridge):**
- **Five consecutive-prime instances** (`andrica_2_3`, `andrica_7_11`, `andrica_23_29`,
  `andrica_89_97`, `andrica_113_127` — including the wide gap-14 case), each proving both
  consecutivity and the integer form (gap−1)² < 4pₙ.
- **The integer ↔ √ equivalence** (`andricaInt_iff_sqrt`): (q−p−1)² < 4p ⟺ √q − √p < 1 — bridging
  the decide-checkable form to the classical statement.

**OPEN.** Whether Andrica's inequality holds for all consecutive primes.

---

## Oppermann's conjecture (open — strengthens Legendre)

**Claim.** For n > 1, is there a prime in both (n²−n, n²) and (n², n²+n)? Open (stronger than
Legendre). Module: `Brockian.OppermannConjecture`. `OppermannConjecture` is an unproven `def`.

**PROVED (concrete + relation):**
- **Nine instances** (`oppermann_2`…`oppermann_10`): a prime in each of the two intervals for
  n = 2…10, with explicit two-sided witnesses.
- **Oppermann ⇒ Legendre** (`oppermannUpper_imp_legendre`): the upper interval (n², n²+n) ⊆
  (n², (n+1)²), so an Oppermann-upper prime is a Legendre prime — a verified *logical relation*
  between two open problems.

**OPEN.** Whether both intervals always contain a prime.

---

## Palindromic primes (infinitude open)

**Claim.** Are there infinitely many base-10 palindromic primes? Open.
Module: `Brockian.PalindromicPrimes`. `PalindromicPrimeInfinitude` is an unproven `def`.

**PROVED (concrete + a full structural theorem):**
- **Ten palindromic primes** (`palindromic_2`, `palindromic_11`, …, `palindromic_919`).
- **Every even-length base-10 palindrome is divisible by 11** (`even_palindrome_dvd_11`) — proved in
  general (induction on `List.Palindrome` + `11 ∣ 1+10^(2k+1)`), not just by example.
- **Capstone: 11 is the only even-length palindromic prime** (`eleven_unique_even_palindromic_prime`).

**OPEN.** Whether infinitely many palindromic primes exist (all but 11 must have odd length).

---

## Fortunate numbers — Fortune's conjecture (open)

**Claim.** Is every Fortunate number prime? (The Fortunate number for a primorial P is the smallest
m > 1 with P+m prime.) Open. Module: `Brockian.FortunateNumbers`. `FortuneConjecture` is an unproven `def`.

**PROVED (concrete):**
- **Four Fortunate numbers** (`fortunate_2`, `fortunate_6`, `fortunate_30`, `fortunate_210`): bases
  2, 6, 30, 210 give Fortunate numbers 3, 5, 7, 13 — each verified as the *smallest* qualifying m.
- Those values are prime (`fortunate_values_prime`), illustrating Fortune's conjecture.
- The bases are the primorials (`primorial_2/3/5/7`, via Mathlib's root-namespace `primorial`).

**OPEN.** Whether every Fortunate number is prime.

---

## Brocard's conjecture — primes between prime squares (open)

**Claim.** Are there always ≥ 4 primes between consecutive prime squares pₙ² and pₙ₊₁² (for pₙ ≥ 3)?
Open. (*Distinct* from Brocard's *problem* n!+1=m², a separate module.)
Module: `Brockian.BrocardGap`. `BrocardGapConjecture` is an unproven `def`.

**PROVED (concrete):**
- **Five instances** (`brocard_3_5`, `brocard_5_7`, `brocard_7_11`, `brocard_11_13`, `brocard_13_17`),
  each exhibiting four increasing primes between the consecutive prime squares (e.g. between 9 and 25:
  11, 13, 17, 19), with consecutivity verified.

**OPEN.** Whether ≥ 4 primes always lie between consecutive prime squares.

---

## Gilbreath's conjecture — prime difference triangle (open)

**Claim.** Iterating adjacent absolute differences on the prime sequence, does every row (k ≥ 1)
start with 1? Open. Module: `Brockian.GilbreathConjecture`. `GilbreathConjecture` is an unproven `def`.

**PROVED (concrete):**
- **Rows 1–10 start with 1** (`gilbreath_row1_head` … `gilbreath_row10_head`) over the first 25
  primes — the leading entry of each iterated difference row equals 1, by pure kernel computation
  (empty axiom set).
- The exact first difference row is recorded (`gilbreath_row1_eq`).

**OPEN.** Whether every row of the prime difference triangle starts with 1.

---

## Weird numbers — does an odd one exist? (open)

**Claim.** Is there an *odd* weird number? (Weird = abundant but not semiperfect; smallest is 70.)
None is known — open, parallel to odd perfect / odd Giuga. Module: `Brockian.WeirdNumbers`.
`OddWeirdExists` is an unproven `def`.

**PROVED (concrete + contrast):**
- **70 and 836 are weird** (`weird_70`, `weird_836`): abundant, and no subset of proper divisors
  sums to n (128- and 2048-subset kernel checks).
- **12 and 20 are abundant *and* semiperfect** (`twelve_not_weird`, `twenty_not_weird`) — showing
  weird is strictly stronger than abundant.

**OPEN.** Whether any odd weird number exists.

---

## Perfect totient numbers (infinitude open)

**Claim.** Are there infinitely many perfect totient numbers (n = φ(n) + φ(φ(n)) + … + 1)? Open.
Module: `Brockian.PerfectTotient`. `PerfectTotientInfinitude` is an unproven `def`.

**PROVED (concrete):**
- **Nine perfect totient numbers** (`pt_3`, `pt_9`, `pt_15`, `pt_27`, `pt_39`, `pt_81`, `pt_111`,
  `pt_183`, `pt_243`) — including the full powers-of-3 chain 3, 9, 27, 81, 243 = 3¹…3⁵, each verified
  by computing the iterated-totient sum.
- A non-example (`not_pt_4`).

**OPEN.** Whether infinitely many perfect totient numbers exist.

---

## Wilson primes (infinitude open)

**Claim.** Are there infinitely many Wilson primes (p² ∣ (p−1)!+1)? Only 5, 13, 563 are known. Open.
Module: `Brockian.WilsonPrimes`. `WilsonPrimeInfinitude` is an unproven `def`.

**PROVED:**
- **5 and 13 are Wilson primes** (`wilson_5`, `wilson_13`; 169 ∣ 12!+1 = 479001601). 563 is beyond
  kernel reach (562! is astronomical), so honestly scoped to the two small ones.
- **Wilson's theorem** (`prime_dvd_factorial_add_one`, via Mathlib's `ZMod.wilsons_lemma`):
  p ∣ (p−1)!+1 for *every* prime — the fact Wilson primes strengthen from p to p².
- A non-example (`seven_not_wilson`: 49 ∤ 6!+1 = 721).

**OPEN.** Whether infinitely many Wilson primes exist.

---

## Quasiperfect numbers — does one exist? (open)

**Claim.** Does a quasiperfect number (σ(n) = 2n+1) exist? None is known — open (if one exists it is
an odd square > 10³⁵). Module: `Brockian.QuasiperfectNumbers`. `QuasiperfectExists` is an unproven `def`.

**PROVED (the three regimes, both known sides):**
- **Every power of 2 is almost-perfect** (`almostPerfect_pow_two`, general theorem): σ(2ᵏ) = 2·2ᵏ − 1.
  Concrete: 1, 2, 16 almost-perfect; 6, 28 perfect (σ = 2n).
- **The three regimes are mutually exclusive** (`not_quasiperfect_of_almostPerfect`,
  `not_quasiperfect_of_perfectσ`) — σ = 2n−1, 2n, 2n+1 are distinct.

**OPEN.** Whether any quasiperfect number (the σ = 2n+1 case) exists — the unknown middle sitting
between the well-understood almost-perfect (−1) and perfect (0) regimes.

---

## Superperfect numbers — does an odd one exist? (open)

**Claim.** Is there an *odd* superperfect number (σ(σ(n)) = 2n)? None is known — open, parallel to
odd perfect. Module: `Brockian.SuperperfectNumbers`. `OddSuperperfectExists` is an unproven `def`.

**PROVED (concrete + Mersenne connection):**
- **2, 4, 16, 64 are superperfect** (`superperfect_2/4/16/64`).
- **2^(p−1) is superperfect when 2^p−1 is a Mersenne prime**
  (`superperfect_two_pow_of_mersenne_prime`): σ(2^(p−1)) = mersenne p, then σ(mersenne p) = 2^p =
  2·2^(p−1) — tying superperfect numbers to Mersenne primes (as with even perfect numbers).
- A non-example (`six_not_superperfect`).

**OPEN.** Whether any odd superperfect number exists.

---

## The discipline

The frontier lane never emits a solved famous conjecture. It emits four honest kinds of output:
unconditional partial results, conditional reductions (named-hypothesis, CONDITIONAL register),
refutation certificates, and precisely-stated open conjectures. Over many cycles this builds a
machine-checked map of *where the hard part actually lives* — which is itself a real contribution.
Regenerate and re-check: `python3 scripts/gen_registry.py && python3 scripts/verify_firewall.py`.
