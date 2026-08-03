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

**Claim.** `φ(n) ∣ (n − 1)` implies n prime. Module: `Brockian.LehmerTotient` *(in progress)*.

**Targeted (necessary conditions on a composite counterexample):** odd; squarefree; ≥ 3 distinct
prime factors. Results will be listed here once verified and integrated.

---

## The discipline

The frontier lane never emits a solved famous conjecture. It emits four honest kinds of output:
unconditional partial results, conditional reductions (named-hypothesis, CONDITIONAL register),
refutation certificates, and precisely-stated open conjectures. Over many cycles this builds a
machine-checked map of *where the hard part actually lives* — which is itself a real contribution.
Regenerate and re-check: `python3 scripts/gen_registry.py && python3 scripts/verify_firewall.py`.
