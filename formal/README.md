# Formal Verification (TLA+ & Lean 4)

This directory contains machine-checked formal specifications and proofs covering the concurrent protocols and safety invariants of `@0xdoublesharp/lru-cache-clustered`.

## TLA+ Models (`formal/tla/`)

Model-checked exhaustively with TLC (`tlc2.TLC`):

| Model                                                  | Source mapped                                 | Properties verified                                                                                                                                                                                                                                                                                                                |
| ------------------------------------------------------ | --------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [`L1Coherence.tla`](./tla/L1Coherence.tla)             | `src/primary.ts`, `src/l1.ts`, `src/index.ts` | `TypeOK`, `VersionBounds`, `NoStaleAfterDrain` (no stale L1 entries once FIFO invalidations drain, including across destroy/recreate and local cancels), `RespectsNamespaceFloor`, and `EventualConvergence` (non-vacuous liveness requiring drained queues).                                                                      |
| [`FetchSingleFlight.tla`](./tla/FetchSingleFlight.tla) | `src/primary.ts`, `src/index.ts`              | `TypeOK`, `AtMostOneLiveLeader`, `LockOwnerConsistent`, `DestroyedNamespaceClean`, `NoOrphanedLockWhenSettled` (including timed-out `fetchClaim` released via `ownerRequestId`), `NoEmptyLock`, `LeaderNotInFollowers`, and `ResolvedFollowersConsistent` (per-follower oversize delivery across `forceRefresh` and lock pruning). |

Run TLC:

```sh
TLA2TOOLS_JAR=/path/to/tla2tools.jar pnpm formal:tla
```

## Lean 4 Proofs (`formal/lean/`)

Machine-checked unbounded proofs (zero `sorry`, zero external dependencies, pinned to `leanprover/lean4:v4.35.0`):

| Module                                                                  | Source mapped                 | Theorems proved                                                                                                                                                                                                                                                                                                           |
| ----------------------------------------------------------------------- | ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [`Formal/L1Coherence.lean`](./lean/Formal/L1Coherence.lean)             | `src/l1.ts`, `src/primary.ts` | Stale-fill rejection (`latestSeen`, existing entry version monotonicity, cancelled read, read fence), key/namespace invalidation floor, and destroy+recreate strict version increase.                                                                                                                                     |
| [`Formal/FetchSingleFlight.lean`](./lean/Formal/FetchSingleFlight.lean) | `src/primary.ts`              | Superseded `fetchStore` non-mutation (after `set`/`delete`/`destroy`/token mismatch), revoked follower generation never leads or recreates destroyed namespaces, `fetchRelease` clears timed-out leader locks, promoted-follower abort pruning, and per-follower oversize `fetchStore` delivery surviving `forceRefresh`. |
| [`Formal/TtlBounds.lean`](./lean/Formal/TtlBounds.lean)                 | `src/index.ts`, `src/l1.ts`   | `normalizeL1Ttl` positivity, `<= primaryTtl` clamp for all inputs, exact preservation of explicit `localL1.ttl` (no silent 100ms inflation), and per-entry remaining-TTL cap.                                                                                                                                             |
| [`Formal/KeyEncoding.lean`](./lean/Formal/KeyEncoding.lean)             | `src/l1.ts` (`encodeL1Key`)   | Tag separation across all 6 key domains (`encodeTaggedKey_injective`) and end-to-end injectivity (`encodeL1Key_injective`) for strings, booleans, signed decimal `Int` bigints, WeakMap `Nat` function/object IDs, and canonical number payloads.                                                                         |

Run Lean 4:

```sh
pnpm formal:lean
```
