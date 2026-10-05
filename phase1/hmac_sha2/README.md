# Phase-1 Proof-of-Life — HMAC-SHA-2

This is the "scale it to a real HMAC/SHA obligation" step the base [`phase1/README.md`](../README.md) names as the next joint engineering. Where the base Phase-1 proves generic crypto idioms, the five obligations here are the **decidable bitvector facts that sit inside HMAC-SHA-256** — proved twice, by two genuinely independent cores, and bound into one hash-sealed, re-checkable certificate.

## The five obligations

| obligation | statement | why it's a real HMAC-SHA-2 fact |
|---|---|---|
| `sha256_ch_spec_eq_impl` | `(x∧y) ⊕ (¬x∧z) = (x∧y) ∨ (¬x∧z)` | SHA-256 **Ch** — the FIPS 180-4 spec (XOR) form equals the constant-time (OR) form an implementation emits |
| `sha256_maj_spec_eq_impl` | `(x∧y)⊕(x∧z)⊕(y∧z) = (x∧y)∨(x∧z)∨(y∧z)` | SHA-256 **Maj** — spec form equals the OR form |
| `hmac_key_pad_difference` | `(k⊕ipad) ⊕ (k⊕opad) = ipad⊕opad` | HMAC's inner/outer padded-key difference is **key-independent** |
| `hmac_pad_xor_const` | `0x36363636 ⊕ 0x5c5c5c5c = 0x6a6a6a6a` | the HMAC pad constants XOR to the fixed `0x6a` per byte |
| `sha256_compress_add_assoc` | `(a+b)+c = a+(b+c)` mod 2³² | the compression fold `T1 = h + Σ₁(e) + Ch + Kₜ + Wₜ` is well-defined because `+` is associative |

`sha256_ch_spec_eq_impl` is the headline: it is exactly the kind of impl-vs-spec equivalence a gate certifies — the FIPS reference writes `Ch` with XOR, a data-oblivious implementation writes it with OR, and here they are proved identical.

## The two independent provers

- **Z3 4.16.0** (SMT/SAT) — runs the SMT-LIB2 query in [`obligations/`](./obligations); asserts the *negation*, `unsat` is the proof. A propositional bit-blast search.
- **Lean 4 kernel + AXLE** — a proof by *different mathematics*, module [`Brockian.HighAssuranceHmacSha2`](../../Brockian/HighAssuranceHmacSha2.lean): per-bit reduction (`BitVec.getLsbD`) + `Bool` case analysis for the bitwise identities, a literal `decide` constant-fold for the pad constant, and `BitVec.add_assoc` for the fold. Re-verified by the AXLE cloud prover (`lean-4.32.2`) and **axiom-audited** (axioms ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorry`/`admit`/`native_decide`, and crucially **no `bv_decide` SAT axiom** — so the Lean leg is not a second SAT solver).

An obligation is **CROSS-VERIFIED** only when both agree. Agreement across two *different methods* (SAT search vs. kernel-checked per-bit reasoning) is stronger evidence than agreement across two SAT engines.

## Run it

```bash
python3 phase1/hmac_sha2/prove.py                          # both provers → emit the certificate
python3 phase1/recheck.py phase1/hmac_sha2/certificate.json  # independent re-verify: hash + re-run the SMT queries
```

`recheck.py` (the shared re-checker) recomputes the SHA-256 over `{provers, obligations}` — edit any statement, query, or verdict and the hash breaks — and re-runs an SMT solver on each embedded query, reproducing the Z3 leg **without our pipeline**. Point it at another solver with `--solver=cvc5` for a third independent check.

Current certificate digest: `b205f29643c4d4cf8092d353de769503f8a4d3f72db7b4f6fdcec2a2e141e87e`.

## Honest scope (stated, not buried)

These are the small, **decidable `QF_BV`** obligations that sit *inside* HMAC-SHA-256 — the round selectors, the key-pad structure, the compression fold's associativity. This is **not** a proof of HMAC-SHA-256 functional correctness, collision resistance, or any security property; those are out of scope for a decision procedure. The point of Phase-1 is the **discipline** on real cryptographic structure — two genuinely independent provers, agreement required, a portable tamper-evident certificate anyone can re-check. The next joint step is a full SAW obligation (e.g. an AWS-LC HMAC-SHA-2 equivalence) carried through the same gate with a proof-carrying certificate.
