# Referee review — five legacy Brockian documents (2026-08-13)

Reviewed at Chris's request ("some may be genuinely new, some may be not novel just
packaged in geometry and others may need work or be false — review and bring over
anything that passes"). Method: five parallel claim-inventory readers (one per doc),
then numerical verification of every checkable claim and registry cross-check.

Documents: (1) "The Brockian Spiral: A Unifying Framework…" (docx), (2) "Patterns and
Proofs in the Brockian Spiral FINAL" (docx; math content lives in 142 images, prose
only reviewed), (3) "Implementation Mathematics V2" (docx), (4) "Elegant rework"
(docx), (5) "The_Curved_Number_Line_Verified.pdf" (July 2026, Aristotle-verified).

## Verdict summary

**Doc 5 is the keeper.** It is the direct precursor of the current program — register-
tagged, Aristotle-verified, self-policing (its §8 failure-mode taxonomy is the ancestor
of our audit practice). Nearly all its verified content already lives in the registry
(constellation tables, q−2 law, golden rigidity, Dirichlet import, MacMahon
one-direction, spectral scaffold). Two errors found IN it:
- **Its Thm 4.1 sexy-prime row is wrong** ("four transitions, count 4") — contradicts
  its own master formula and numerics: sexy primes > 5 have exactly THREE roads
  (1→2, 2→3, 3→4). Our page and fleet target carry the correct count.
- **"Pentagon-ray primes ⊂ {1,9,11,19} mod 20" is false as printed** (7 is a
  counterexample) but TRUE when restricted to the square rays (p ≡ 1, 4 mod 5):
  rescued, verified to 2·10⁵, queued as Brockian.ConeLine.square_ray_primes_mod20.

**Docs 1–4: the mathematics that is true is standard; the mathematics that would be
new is false, ill-defined, or circular.** The durable value is presentational (the
construction pedagogy, the count-by star patterns, the Cone of Light image, heatmap /
explorer UI ideas) — all already flowing into /labs/number-line.

## Brought over (verified before crossing)

1. **Fibonacci uniform distribution mod 5** (rescued by Chris's correction): each ray
   receives exactly 4 of every 20 Fibonacci numbers; verified; moduli 5, 25, 125
   uniform, all others tested non-uniform — matches the classical theorem that 5^k are
   the ONLY uniform moduli (Kuipers–Shiue 1972; Niederreiter 1972). → gallery copy +
   fleet target Brockian.ConeLine.fib_uniform_mod5.
2. **Square-ray primes mod 20** (rescued from doc 5's misstatement). → fleet target.
3. **"Cone of Light"** — Chris's own name for the signed double cone (doc 1). → adopt
   in Cone section copy.
4. **The well-defined Brockian zeta** ζ_B(s) = Σ e^{2πi((n−1) mod 5)/5} n^{−s}
   (doc 4's version; doc 1's version is ill-defined — complex exponent of a complex
   number). Doc 4's OWN residue computation is essentially correct and shows the
   zero-mean twist CANCELS the pole at s=1 → ζ_B is entire — which REFUTES doc 4's own
   "pole at s=1" headline. The honest story is genuinely elegant: a zeta with no pole,
   decomposing into Hurwitz zetas; and the Davenport–Heilbronn lesson (our machinery
   program's own negative control) says we must NOT expect its zeros on a line.
   → candidate future lab note: "The Brockian zeta is entire — and why we don't claim
   its zeros align." NOT claimed beyond that.

## Graveyard (named, with reasons — per the contract)

- G-LEG-1: Brockian Spiral as fractal (docs 1,4): smooth curve, dimension 1; no
  computation ever produced. Load-bearing for the Bell/quantum sections → those fall.
- G-LEG-2: "Thm 5.1" RH transfer (doc 1): circular — assumes the map's defining
  property AND classical RH, then boxes the conjecture as QED.
- G-LEG-3: ζ_B of doc 1 (e^{2πiB(n)} with complex B(n)): terms blow up like e^{2πkn};
  series diverges everywhere; continuation/functional-equation "proofs" vacuous.
- G-LEG-4: Bell/no-cloning/QKD/post-quantum-crypto claims (docs 1,2,3): analogy
  presented as theorem; ECC-vs-Shor claim inverted; key-exchange protocol (doc 3)
  non-executable by its own honest parties.
- G-LEG-5: Doc 3's numerical "H4 verification" (1,000 eigenvalues ≈ zeta zeros):
  contradicts its own Weyl law by ~10³ in scale, placeholder provenance hashes,
  S-independence destroys its own crypto chapter. Treated as fabricated.
- G-LEG-6: Doc 3 spectral-geometry errors: Γ₀(5) "no elliptic points" (ν₂=2), cusp
  forms in (0,1/4) (inverted), ‖V‖ ~ log log P (Mertens gives log P), "multiplication
  operator is smoothing" (false), three inconsistent heat-trace constants.
- G-LEG-7: Doc 4 local errors: rotation formula (θ(n+5)=θ(n), not +2π/5), terminal-
  digit star-pattern vertex orders (impossible under its own map; true only for
  multiples sequences), Fibonacci index/value confusion, cubic residue table (3 of 4
  entries wrong; cubes hit EVERY ray — bijection, worth showing as a contrast fact),
  "F_n and F_{n+5} share a vertex" (period is 20), scalar functional equation
  (Hurwitz decomposition gives a matrix relation).
- G-LEG-8: Doc 2 "ring = Pisano period" (a ring holds 5 integers; the period is 20 in
  the index) — though the uniform-spread half was RIGHT and is rescued above.
- G-LEG-9: Priority claims ("first rigorous connection between modular spectra and
  zeta zeros" — Selberg/Connes precede; "25 theorems with complete rigor";
  "reproduced by five independent groups" with no names).

## Method note

Every rescue was numerically verified before queueing; every kill is specific (formula,
counterexample, or internal contradiction). The docs' own best practice (doc 5's
registers and failure taxonomy) is already institutionalized in the current program.
