# Identifiability before ontology

## Question

Suppose a recognizer is available only through a family of interventions or
tests `T`, with outputs in `O`. A realization is a pairing

\[
e : H \times T \to O,
\]

where `H` is a proposed state space. Which structure on `H` is determined by
the observations?

The answer is: not the raw state space. The first obstruction is a silent
extension. Replace `H` by

\[
\widetilde H = H \times \mathbf 2
\]

and define

\[
\widetilde e((h,b),t)=e(h,t).
\]

All specified tests agree exactly, yet `(h, false)` and `(h, true)` remain
distinct internal states. `ObservationalNonidentifiability.lean` formalizes
this construction and proves that every inhabited observation system admits
such a non-extensional realization.

## What the theorem does and does not say

This is an elementary obstruction, not yet the paper's novelty theorem. It
rules out inference from black-box agreement directly to a unique internal
ontology, path space, or monad. It does **not** rule out reconstruction after a
minimality or test-completeness condition is imposed.

The observation-generated object is instead the extensional collapse

\[
H/{\sim_e},
\qquad
h\sim_e h' \iff \forall t,\ e(h,t)=e(h',t).
\]

Any claim about recognition paths must therefore live either:

1. on this quotient;
2. on additional intervention structure proven to separate states; or
3. on a chosen realization, explicitly acknowledged as non-identifiable.

## Strong target theorem

The next target is not another arbitrary latent model. Define a category of
realizations of one observation table, with observation-preserving maps. Then
prove a minimal-realization theorem of the following form:

> If the intervention family is closed under the relevant contexts, the
> extensional collapse is terminal among reduced realizations (or unique up to
> the appropriate equivalence). Without that completeness, construct two
> reduced realizations having the same finite observation table but different
> continuation/path structure.

The finite-table counterexample is the practically relevant half: it turns
“black box” from a slogan into a precise boundary between what experiments can
identify and what remains gauge freedom.

## Consequence for monads

A monad must not be selected as a container for hidden behavior. First recover
observable operations and equations from the contextual/interventional
closure. A monad becomes justified only if those operations present an
algebraic theory whose free construction is empirically invariant. Different
silent extensions may carry inequivalent monadic or path structure while
having the same observations, so raw black-box data cannot select one without
an identifiability theorem.
