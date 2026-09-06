# Recognition Paths

Recognition Paths studies when formal identity can be transported into the
observational identity of a recognizer.

The project starts from two observations of a shared syntax rather than from a
chosen latent-state model:

- a formal semantics, which induces logical contextual equivalence;
- a recognizer, which induces behavioral contextual equivalence.

Their quotient maps create a canonical correspondence. Whether that
correspondence descends to a function, monoid morphism, enriched functor, or
equivalence is a mathematical property to prove or test.

## First construction

For setoids `L` and `B` on a common syntax `X`, write `L.Refines B` when

```text
L x y -> B x y.
```

This condition holds exactly when the canonical assignment

```text
[x]_L |-> [x]_B
```

is well-defined. `RecognitionPaths/Factorization.lean` formalizes this result
and its uniqueness.

## The fixed small world

`RecognitionPaths/Horn.lean` fixes a small Horn language `Σ`, ordered premise
traces `Σ*`, queries, semantic entailment, and theory-level logical identity
`u ≡_L v` (the same consequences for every query). It proves that
permutations are logically identical and that `≡_L` is a congruence, so the
logical meaning space `L = Σ*/≡_L` is a monoid.

`RecognitionPaths/Recognition.lean` defines a recognizer `ρ : Σ* × Q → O`,
right-context identity `u ≡_ρ v`, two-sided identity `u ≈_ρ v`, and the
behavioral meaning space `B = Σ*/≈_ρ`, which is again a monoid. The
Recognition Factorization Theorem is then instantiated: `≡_L ⊆ ≈_ρ` holds
exactly when a unique representative-preserving map `F : L → B` exists, and
that map is a monoid morphism. The reverse inclusion gives `G : B → L`, and
both together give `L ≃ B`. Since `L` is commutative and idempotent, the
inclusion `≡_L ⊆ ≈_ρ` forces `uv ≈_ρ vu` and `ww ≈_ρ w`: invariance has
falsifiable equational consequences.

`RecognitionPaths/Nerode.lean` proves that the right-context quotient
`Σ*/≡_ρ` is the extensional collapse of the prefix realization of `ρ`, so
the identifiable state object of the obstruction below is the Nerode
quotient, and `B` acts on it as its transition monoid.

`RecognitionPaths/Biextensional.lean` adds the column-side quotient: tests
modulo equal state profiles. Together with the state collapse this is the
biextensional collapse of the observation Chu space, in which tests
separate states and states separate tests.

`RecognitionPaths/Identification.lean` gives the finite-test criterion: a test
family containing the direct queries induces exactly `≡_ρ` if and only if the
identity it induces is closed under appending one symbol, and a closure
failure yields the separating test to add next. See
`docs/RECOGNITION_PATH_FOUNDATIONS.md`.

## Research layers

1. Exact contextual equivalence and quotient factorization.
2. Quantitative equivalence and Lawvere-enriched geometry.
3. Hankel/Chu reconstruction of behavioral state from prefix-test observations.
4. Coherent transport of logical paths into recognition paths.
5. Algebraic operations and equations induced by observation; monads are
   reconstructed only after this theory is identified.

## First obstruction

`RecognitionPaths/ObservationalNonidentifiability.lean` proves the elementary
silent-extension obstruction. Any inhabited realization can be replaced by a
realization with an extra hidden Boolean coordinate while preserving every
specified observation. The extension is non-extensional, so observations do
not determine a unique raw state space or path structure.

This makes the next objective precise: construct the observation-generated
extensional collapse, and determine the intervention-completeness assumptions
under which a minimal realization is unique. See `docs/IDENTIFIABILITY.md`.

`RecognitionPaths/ExtensionalCollapse.lean` completes the first half: it
constructs the quotient by equality of complete test profiles, proves its
extensionality and universal factorization property, and proves that silent
extensions have equivalent collapses. The remaining problem is whether a
finite experimental test family determines the same collapse as the full
contextual family.

## Status

This repository contains foundations and conjectures for an active research
program. Existing terminology from type theory, automata, coalgebra, enriched
category theory, and system realization is kept distinct from new definitions.

## Build

Install Lean through `elan`, then run:

```bash
lake build
```
