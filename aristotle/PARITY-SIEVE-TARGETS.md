# Parity/sieve Aristotle targets (Tao-guided wave, 2026-08-04)

All TRUE, self-contained, Mathlib-vetted as MISSING before submit. Verify returns at AXLE @4.32
(axiom-clean) before integration. Owner: Claude (parity/sieve lane; NOT the operator lane, NOT
Codex's SieveSpectrumDeletion per-component lane).

| Project ID | Dir | Theorems | Status |
|---|---|---|---|
| `6047b082-ce7f-4dfd-979e-444f56050851` | `aristotle/liouville-parity` | `liouville_divisor_sum` (∑_{d∣n} λ(d) = [IsSquare n]); `squarefree_divisor_count` (∑ μ(d)² = 2^ω(n)) | INTEGRATED (working tree, AXLE @4.32) |
| `806823f1-4093-4f54-bd6a-ad4a91d6de93` | `aristotle/squarefree-square-divisors` | `moebius_sq_eq_sum_sq_divisors` (μ(n)²=∑_{d²∣n}μ d); `liouville_eq_sum_moebius_sq_divisors` (λ=∑_{d²∣n}μ(n/d²)) | INTEGRATED (working tree, AXLE @4.32) |
| `06a22f46-b909-4f14-b637-2e5749236ef5` | `aristotle/legendre-sieve` | `legendre_sieve` (#{n≤x: (n,P)=1} = ∑_{d∣P} μ(d)⌊x/d⌋) | INTEGRATED (working tree, AXLE @4.32) |

Harvest: `aristotle download <id> --destination <f>`; AXLE-verify each decl @lean-4.32.0; integrate
passers as `Brockian/<Module>.lean` via the ritual (no_theater_lint → attest → verdicts.yaml →
Brockian.lean import → gen_registry ×2). Reject any sorry/phantom/axiom-probe failure; re-queue via
`aristotle continue`.

## Wave 2 (2026-08-04) — deeper sieve identities

Note: Mathlib already has `NumberTheory/SelbergSieve.lean` (weighted upper-bound framework) — these
are the ELEMENTARY complementary identities it does not contain. All Mathlib-vetted as missing.

| Project ID | Dir | Theorem | Status |
|---|---|---|---|
| `5edf33d8-b18e-4c4d-8ff2-0050459c5109` | `aristotle/squarefree-count` | `squarefree_count` (#{n≤x: Squarefree} = ∑_{d²≤x} μ(d)⌊x/d²⌋) | INTEGRATED (AXLE @4.32) |
| `dbcb784d-0028-4491-b4c4-1cbdd06401cb` | `aristotle/legendre-error` | `legendre_sieve_error` (\|#coprime − x∏(1−1/p)\| ≤ 2^ω(P)) | INTEGRATED (AXLE @4.32) |
| `85669593-a947-4095-ab03-1e3aec4219d9` | `aristotle/totient-moebius` | `totient_eq_sum_moebius` (φ(n)=∑_{d∣n} μ(d)(n/d)) | INTEGRATED (AXLE @4.32) |

Same harvest ritual + 4.28→4.32 port watch (strip any local re-defs Mathlib now ships).
