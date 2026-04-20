# Adversarial Review — Isabelle AFP Entry: Nagata Factoriality

**Scope:** `isabelle/Nagata-Factoriality/` — the actual AFP publication target,
including `document/root.tex`, `document/root.bib`, all six `.thy` files, and
the `ROOT` session definition.

---

## 1. Hallucination / Unsupported Claims

**Verdict: No hallucinations found.**

Every claim in the abstract and overview was cross-checked against the
corresponding Isabelle theory.

| Claim in manuscript | Evidence in theories |
|---|---|
| Prime-generated multiplicative sets | `Prime_Generated.thy`: `prime_generated`, `mult_submonoid_closure`, `powers_set` |
| Wrapper around `Localization_Ring` | `Localization_Interface.thy`: `fraction_eq_iff_rel`, `fraction_surj`, `dvd_map_iff`, `map_inj_on`, etc. |
| Record-based descent: prime-generated | `Nagata_Lemmas.thy`: `nagata_theorem` (line 1849) |
| Record-based descent: prime-or-unit | `Nagata_Lemmas.thy`: `nagata_theorem_of_prime_or_unit` (line 1893) |
| Closure corollaries: arbitrary generators | `nagata_theorem_of_prime_generators` (line 1935) |
| Closure corollaries: finite generators | `nagata_theorem_of_finite_prime_generators` (line 1950) |
| Polynomial application: away from X | `Polynomial_Applications.thy`: `polynomial_factorial_of_localized_X_factorial` |
| Polynomial application: constant primes | `Fraction_Field_Applications.thy`: `polynomial_factorial_of_localized_constant_primes_factorial` |
| Noetherian domain hypothesis | All four Nagata theorems assume `noetherian_domain R` |

---

## 2. Correctness

**Verdict: Correct, assuming the Isabelle session builds.**

The proofs are machine-checked.  The key logical chain is:
1. `prime_generated S` → every irreducible that divides into S is prime
   (`prime_of_irreducible_of_dvd_mem_prime_generated`).
2. If an irreducible `p` avoids `S`, it stays irreducible in the localization
   (`localization_irreducible_of_irreducible_prime_generated`).
3. In a UFD localization, irreducibles are prime, so `p` is prime in the
   localization, and the descent lemma pulls this back
   (`prime_of_localization_prime_prime_generated`).
4. Every irreducible in R is prime → R is a UFD (via `noetherian_domain`
   providing the ACC/factorization-existence half).

No unsound `sorry` or `oops` found in any `.thy` file.

---

## 3. Completeness

**Verdict: Adequate for an AFP entry.  One structural note.**

The entry proves both the prime-generated and the prime-or-unit variants of
Nagata's theorem, plus closure corollaries, plus two polynomial applications.
This is a solid scope for an AFP entry.

**Minor gap (not a blocker):** The polynomial applications assume
`noetherian_domain (K[X])` and `ring_prime` for X (or constant primes) as
hypotheses rather than deriving these from `noetherian_domain R` + subfield/subring
conditions.  This is a reasonable design choice—the applications are
"abstract application templates" rather than fully self-contained end-to-end
corollaries.  The `polynomial_prime_X` lemma does derive primality of X from
`subfield K R`, so the field case is fully closed.

---

## 4. Language / Exposition

### Issues found and fixed in this PR

| # | Severity | Issue | Location | Fix |
|---|----------|-------|----------|-----|
| L1 | **Medium** | "localization away the polynomial variable" — missing preposition | `root.tex` abstract (line 28), overview (line 42); `Nagata_Factoriality.thy` (line 29) | → "away from" (3 sites) |
| L2 | **Low** | Bare `\cite` without tilde/space: `Matsumura.\cite{...}` | `root.tex` line 39 | → per-author `~\cite{}` with non-breaking spaces |
| L3 | **Low** | Process language ("now") in theory text | `Nagata_Factoriality.thy` lines 22, 25 | Removed "now" |
| L4 | **Low** | Overview section was a single paragraph almost duplicating the abstract | `root.tex` §Overview | Expanded with central-result statement and per-theory structural map |

### Not an issue

- The abstract uses "record-based" to describe the HOL-Algebra proof style.
  This is accurate and standard Isabelle terminology.
- The theory-level text blocks use `@{thm [display] ...}` antiquotations
  extensively.  These render as full theorem statements in the AFP document
  and are idiomatic.

---

## 5. Plagiarism / Originality

**Verdict: No concerns.**

The formalization is original Isabelle/HOL work built on top of the existing
AFP entry `Localization_Ring` and the `HOL-Algebra` / `HOL-Computational_Algebra`
libraries.  The mathematical content (Nagata's theorem) is classical, and the
manuscript attributes it correctly to Nagata, Samuel, and Matsumura.  No text
appears to be copied from other AFP entries or publications.

---

## 6. Reference-by-Reference Audit

### Nagata1962

- **Used in:** `root.tex` overview, `Nagata_Factoriality.thy` theory text.
- **Pin strength:** Strong.  Nagata's original monograph is the source of the
  eponymous theorem.  The formalization follows the structure of the classical
  proof (descent of primality from localization to base ring).
- **Bibliographic data:** Correct (Interscience, 1962, vol. 13).

### Samuel1964

- **Used in:** `root.tex` overview, `Nagata_Factoriality.thy` theory text.
- **Pin strength:** Strong.  Samuel's lecture notes give a detailed treatment of
  UFDs and the prime-factorization approach that the formalization follows.
- **Bibliographic data:** Correct (Tata Institute, 1964, vol. 30).

### Matsumura1986

- **Used in:** `root.tex` overview only (not cited in any `.thy` file).
- **Pin strength:** Adequate but weak.  Matsumura's book is a standard textbook
  reference for commutative ring theory including localization, but the
  formalization does not follow any specific theorem from Matsumura that isn't
  already attributed to Nagata or Samuel.  The citation is defensible as
  general background but could be strengthened with a specific section
  reference (e.g., §20 "UFDs").
- **Bibliographic data:** Correct (Cambridge, 1986, vol. 8).  Note: the
  `README.md` says "1989" which is a later printing; the bib entry's 1986 is
  the correct first English edition.

---

## 7. Artifact / Reproducibility

**Verdict: Good, with one note.**

- The `ROOT` file correctly declares the session `Nagata-Factoriality` in
  chapter `AFP` with dependency on `HOL-Computational_Algebra` and
  `Localization_Ring`.
- The 1800-second timeout is generous but reasonable for the large inductive
  proofs in `Nagata_Lemmas.thy`.
- The `README.md` provides a working `isabelle build` command with AFP path.
- **Note:** No CI workflow currently builds the Isabelle session.  The Lean
  project has CI but the Isabelle session is not verified in CI.  This is
  common for AFP submissions (the AFP itself runs the build) but worth noting.

---

## 8. Venue / Packaging

**Verdict: Ready for AFP submission, modulo the fixes in this PR.**

- Session structure follows AFP conventions (chapter `AFP`, single
  `document_files` block, `root.tex` + `root.bib`).
- The title "Nagata Factoriality" is terse but acceptable for AFP.
- Author/maintainer metadata is present and correct.
- The `\isabellestyle{it}` and `pdfsetup` packages are standard AFP boilerplate.

---

## 9. Prioritized Fixes

### Already fixed in this PR

1. **[Medium]** Grammar: "localization away X" → "away from X" (3 sites)
2. **[Low]** LaTeX citation spacing (bare `\cite` → `~\cite`)
3. **[Low]** Process language removal ("now")
4. **[Low]** Overview expanded from one paragraph to substantive structural description

### Remaining recommendations (not blocking)

5. **[Info]** Matsumura citation could be pinned to a specific section (e.g., §20).
6. **[Info]** `README.md` says Matsumura 1989; bib correctly says 1986.
   Consider aligning the README.
7. **[Info]** No Isabelle CI — acceptable for AFP submission but would
   strengthen the artifact.

---

## Summary

The Isabelle AFP entry is **substantively sound**.  All manuscript claims are
backed by machine-checked proofs.  The bibliography is correct.  No
hallucinations, plagiarism, or correctness issues were found.

The issues identified are all **exposition-level**: a missing preposition
repeated in three places, citation formatting, process language, and a thin
overview section.  All four have been fixed in this PR.  The remaining
recommendations are informational and not blocking for publication.
