# Foundations: syntax first, quotients second

## Primitive data

Let `X` be a shared syntax. A formal semantics and a recognizer induce two
contextual equivalence relations on `X`:

\[
x \sim_L y,
\qquad
x \sim_R y.
\]

The first theorem assumes only these setoids. It does not assume a transformer,
a latent state, a state monad, or a group representation.

## Canonical correspondence

The syntax determines a jointly surjective relation

\[
\mathcal C_{L,R}
=\{([x]_L,[x]_R):x\in X\}
\subseteq X/{\sim_L}\times X/{\sim_R}.
\]

This relation is the starting path between the two quotients. It becomes a
function from logical classes to recognition classes precisely when

\[
\sim_L\;\subseteq\;\sim_R.
\]

It becomes a function in the reverse direction precisely when
\(\sim_R\subseteq\sim_L\). Both hold exactly when the two equivalence
relations coincide.

## Recognition path notation

For a recognizer \(\rho_a:X\to\mathcal R_a\), define

\[
\Pi_a^\rho(x,y)
:=\operatorname{Id}_{\mathcal R_a}(\rho_a x,\rho_a y).
\]

The notation records a path type, not merely a Boolean equality judgment. A
future homotopical formalization should distinguish:

1. inhabitation of each recognition path type;
2. a selected transport \(\Theta_a(p)\) for every logical path \(p\);
3. coherence of that selection with identity, inverse, and composition.

The current Lean file proves only the set-level quotient theorem. It makes no
claim that this theorem already supplies higher coherent transport.

## Next mathematical target

Given an observation pairing

\[
e:H\times T\to O,
\]

construct its extensional collapse, contextual transition monoid, behavioral
pseudometric, and Hankel realization. Then compare the resulting recognition
quotient with the independently constructed logical quotient.

The monad question comes after identifying the observable operations and their
equations: determine whether they present an algebraic theory whose free/forgetful
adjunction induces a monad, and whether logical path transport lifts to its
Kleisli or Eilenberg–Moore structure.
