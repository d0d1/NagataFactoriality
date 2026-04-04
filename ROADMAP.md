# Roadmap to Publication-Ready Formalization

## Current State
- Nagata's Factoriality Theorem proved with zero sorry (1,600 lines)
- Custom algebra framework (not Mathlib)
- Codex audit: real proof, mathematically sound, ecosystem-isolated

---

## Phase 1: Mathlib Migration (BLOCKER — needs disk space)

**Goal:** Replace all custom definitions with Mathlib types.

### 1.1 Infrastructure
- [ ] Free disk space on dev machine OR use Azure VM / cloud machine
- [ ] Add `require mathlib` to lakefile.lean (done, untested)
- [ ] Run `lake update && lake exe cache get` successfully
- [ ] Verify Mathlib builds

### 1.2 Type Bridges (in order)
Each step: replace custom def → use Mathlib's → fix downstream proofs.

| Custom | Mathlib | Difficulty |
|--------|---------|------------|
| `IntegralDomain` | `[CommRing R] [IsDomain R]` | Easy |
| `dvd` | `Dvd.dvd` (∣) | Easy (exact match) |
| `IsUnit` | `IsUnit` (bundled units) | Easy |
| `Associated` | `Associated` (bundled) | Easy |
| `Irreducible` | `Irreducible` (drop `p ≠ 0`) | Easy |
| `Prime` | `Prime` | Easy |
| `Ideal` | `Ideal R` (= `Submodule R R`) | Medium |
| `NoetherianRing` | `IsNoetherianRing R` | Medium |
| `MultSet` | `Submonoid R` + `0 ∉ S` | Medium |
| `Localization` | `Localization S` + `IsLocalization` | Hard |
| `HasFactorization` | `WfDvdMonoid` + `exists_factors` | Hard |
| `UFD` | `UniqueFactorizationMonoid` | Hard |
| `RingHom` | `RingHom` (Mathlib's) | Easy |

### 1.3 Main Theorem Restatement
- [ ] Restate `nagata_theorem` using only Mathlib types:
```lean
theorem nagata_theorem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD : UniqueFactorizationMonoid (Localization S)) :
    UniqueFactorizationMonoid R
```
- [ ] Verify the proof still goes through with Mathlib API

---

## Phase 2: Uniqueness of Factorization

**Goal:** Prove the "U" in UFD actually works.

- [ ] Define factorization equivalence (same irreducibles up to `Associated` and permutation)
- [ ] Prove: if irreducible = prime, then factorizations are unique up to associates and reordering
- [ ] Connect to Mathlib's `UniqueFactorizationMonoid.factors` and `Multiset.Rel Associated`
- [ ] Prove `factors_unique` theorem

---

## Phase 3: Applications and Corollaries

**Goal:** Show the theorem is useful.

### 3.1 Gauss's Lemma
- [ ] Define polynomial ring `R[X]` (or use Mathlib's `Polynomial R`)
- [ ] Prove content of a polynomial
- [ ] Prove Gauss's lemma: product of primitive polynomials is primitive
- [ ] Corollary: `R` UFD → `R[X]` UFD (classic application of Nagata)

### 3.2 Laurent Polynomials
- [ ] `R` UFD → `R[X, X⁻¹]` UFD (as localization of `R[X]` at `{Xⁿ}`)

### 3.3 Concrete Examples
- [ ] `ℤ` is a UFD (trivial but good test)
- [ ] `ℤ[X]` is a UFD (via Nagata + ℤ is Noetherian + ℚ[X] is a PID)
- [ ] `k[X₁, ..., Xₙ]` is a UFD (iterated application)

---

## Phase 4: Documentation and Paper

**Goal:** Write a publishable paper.

### 4.1 Paper Structure
- [ ] Introduction: why Nagata's theorem, why formalize it
- [ ] Related work: existing Lean/Coq/Isabelle formalizations of UFD theory
- [ ] Proof outline: how the formalization is structured
- [ ] Design decisions: why this proof strategy, comparison with alternatives
- [ ] Lessons learned: what was easy/hard to formalize
- [ ] Statistics: LOC, theorem count, build time

### 4.2 Comparison with Existing Work
- [ ] Check if Mathlib already has Nagata's theorem (it may!)
- [ ] If yes: what does our approach contribute? (Different proof? Better API?)
- [ ] If no: this is a genuine contribution to Mathlib
- [ ] Check Isabelle AFP, Coq stdlib/MathComp for prior art

### 4.3 Mathlib PR
- [ ] If Nagata's theorem is NOT in Mathlib: prepare a Mathlib PR
- [ ] Follow Mathlib contribution guidelines (style, naming, module structure)
- [ ] Get review from Mathlib maintainers

---

## Phase 5: Extensions (Optional, Post-Publication)

- [ ] Nagata's theorem for non-Noetherian rings (Gilmer's generalization)
- [ ] Krull's theorem: Noetherian domain is UFD iff every height-1 prime is principal
- [ ] Connection to class groups: R is UFD iff Cl(R) = 0
- [ ] Dedekind domains and unique factorization of ideals

---

## Priority Order

1. **Phase 1** (Mathlib migration) — everything depends on this
2. **Phase 2** (uniqueness) — mathematical completeness
3. **Phase 4.2** (check existing work) — do this EARLY to avoid duplicating
4. **Phase 3.1** (Gauss's lemma) — strongest corollary
5. **Phase 4** (paper) — write up results
6. **Phase 5** (extensions) — if time permits

## Estimated Effort
- Phase 1: 2-3 days (mostly fighting Mathlib API)
- Phase 2: 1 day
- Phase 3: 2-3 days
- Phase 4: 3-5 days (writing)
- Total: ~2 weeks to publication-ready
