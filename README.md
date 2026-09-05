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

## Research layers

1. Exact contextual equivalence and quotient factorization.
2. Quantitative equivalence and Lawvere-enriched geometry.
3. Hankel/Chu reconstruction of behavioral state from prefix-test observations.
4. Coherent transport of logical paths into recognition paths.
5. Algebraic operations and equations induced by observation; monads are
   reconstructed only after this theory is identified.

## Status

This repository contains foundations and conjectures for an active research
program. Existing terminology from type theory, automata, coalgebra, enriched
category theory, and system realization is kept distinct from new definitions.

## Build

Install Lean through `elan`, then run:

```bash
lake build
```
