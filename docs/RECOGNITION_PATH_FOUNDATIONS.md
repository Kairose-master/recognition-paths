# Recognition path foundations: one small world, three definitions, one theorem

This note fixes a single small mathematical world and states, inside it, what
"logically identical" and "recognized as identical" mean. Everything below is
machine-checked in `RecognitionPaths/Horn.lean`,
`RecognitionPaths/Recognition.lean`, and `RecognitionPaths/Factorization.lean`
unless marked otherwise. No monad is chosen and no model is run.

## 1. The common input language

The signature is a small Horn logic over a type of atoms:

\[
\Sigma=\{A\to B,\; A\land B\to C,\; A\to B\land C,\dots\}.
\]

In Lean a clause is `HornClause Atom` with a `body` and a `head`, both lists of
atoms. An ordered premise trace is a word

\[
w=p_1p_2\cdots p_n\in\Sigma^\ast,
\]

represented as `Trace Atom := List (HornClause Atom)`.

A query `q : Query Atom` is a pair of hypothesis atoms and a goal atom, read
"do the hypotheses together with the theory force the goal?"

The observation space `O` is left abstract. The intended instance is
\(O=\mathbb R^2\), carrying both the YES and the NO logit, so no information
is discarded by taking a margin. A recognizer is

\[
\rho:\Sigma^\ast\times Q\to O,
\]

`Recognizer Sym Q O` with a single field `observe`.

## 2. Logical identity

Write \(\Gamma(w)\) for the Horn theory of `w` with order forgotten
(`Horn.theory`: the set of clauses occurring in `w`). Entailment is semantic:
every valuation that models \(\Gamma\) and makes the hypotheses true makes the
goal true (`Horn.Entails`).

\[
\boxed{
u\equiv_{\mathsf L}v
\iff
\forall q\in Q,\quad
\operatorname{Entails}(\Gamma(u),q)
\iff
\operatorname{Entails}(\Gamma(v),q)
}
\]

This is theory-level identity, not agreement on the one query used in an
experiment. The logical meaning space is

\[
\boxed{L=\Sigma^\ast/{\equiv_{\mathsf L}}}
\qquad
\text{(`Horn.LogicalSpace`)}.
\]

Two facts are proved about it.

- **Permutation invariance** (`Horn.logicalEquiv_of_perm`): if `u` is a
  permutation of `v`, then \(u\equiv_{\mathsf L}v\). This is the formal content
  of "same formal problem" behind every premise-order experiment.
- **Congruence** (`Horn.logicalEquiv_congr`): \(u\equiv_{\mathsf L}v\) implies
  \(xuz\equiv_{\mathsf L}xvz\). The proof goes through the observation that
  theories with the same consequences have the same models, because every
  clause is one of its own consequences. Consequently `L` is a monoid
  (`Horn.LogicalSpace.mul`).

## 3. Recognition identity

Right-context behavioral identity:

\[
\boxed{
u\equiv_\rho v
\iff
\forall z\in\Sigma^\ast,\;\forall q\in Q,\quad
\rho(uz,q)=\rho(vz,q)
}
\qquad
\text{(`Recognizer.RightEquiv`)}.
\]

Two-sided behavioral identity, which also covers replacement in the middle
of a trace:

\[
\boxed{
u\approx_\rho v
\iff
\forall x,z\in\Sigma^\ast,\;\forall q\in Q,\quad
\rho(xuz,q)=\rho(xvz,q)
}
\qquad
\text{(`Recognizer.ContextEquiv`)}.
\]

The behavioral meaning space is

\[
\boxed{B=\Sigma^\ast/{\approx_\rho}}
\qquad
\text{(`Recognizer.Behavior`)}.
\]

`B` is built from external behavior alone; it never names an internal state.
Because \(\approx_\rho\) is a two-sided congruence
(`Recognizer.contextEquiv_append`), concatenation descends to `B` and the
monoid laws hold (`Behavior.mul_assoc`, `Behavior.one_mul`,
`Behavior.mul_one`).

Experiments only observe a finite family of contexts. The restricted relation
\(\approx_{\rho,T}\) (`Recognizer.ContextEquivOn`) is coarser than
\(\approx_\rho\) (`contextEquivOn_of_contextEquiv`) and gets finer as `T`
grows (`contextEquivOn_mono`). Whether some finite `T` recovers
\(\approx_\rho\) is the open identifiability question of
`docs/IDENTIFIABILITY.md`.

## 4. Recognition Factorization Theorem

**Theorem** (`Horn.recognition_factorization`). The following are equivalent.

\[
\boxed{\equiv_{\mathsf L}\subseteq\approx_\rho}
\qquad\Longleftrightarrow\qquad
\boxed{
\exists!\,F:L\to B
\quad\text{such that}\quad
F([w]_{\mathsf L})=[w]_\rho .
}
\]

*Proof.* Forward: if \([w]_{\mathsf L}=[v]_{\mathsf L}\) then
\(w\equiv_{\mathsf L}v\), hence \(w\approx_\rho v\), hence
\([w]_\rho=[v]_\rho\); so the assignment is independent of the representative.
Backward: if such an `F` exists and \(w\equiv_{\mathsf L}v\), then
\([w]_\rho=F([w]_{\mathsf L})=F([v]_{\mathsf L})=[v]_\rho\), so
\(w\approx_\rho v\). Uniqueness follows because the projection
\(\Sigma^\ast\to L\) is surjective. In Lean the statement is the instance of
the setoid-level `recognition_factorization_iff` at the two setoids
`logicalSetoid Atom` and `ρ.contextSetoid`. ∎

The map `F` is `Horn.recognitionMap`. It is a monoid morphism
(`Horn.recognitionMap_mul`): the canonical recognition path respects
concatenation.

The theorem says precisely that

> the model recognizes logically identical inputs as identical

is the same statement as

> there is a canonical path from the logical meaning space to the behavioral
> meaning space.

## 5. Direction matters

| Inclusion | Map | Meaning | Lean |
|---|---|---|---|
| \(\equiv_{\mathsf L}\subseteq\approx_\rho\) | \(F:L\to B\) | logically identical inputs are recognized as identical | `LogicallyInvariant`, `recognition_factorization` |
| \(\approx_\rho\subseteq\equiv_{\mathsf L}\) | \(G:B\to L\) | logical meaning is recoverable from behavior | `LogicallyRecoverable`, `recognition_recovery` |
| both | \(L\cong B\) | the two meaning spaces coincide | `recognitionEquiv` |

The permutation experiments so far probe the first inclusion on a finite
restriction and suggest that it may fail. The second inclusion has not been
tested at all.

## 5a. The Nerode quotient is the identifiable state object

`RecognitionPaths/Nerode.lean` joins the two halves of the library. The
recognizer has a raw *prefix realization*: states are prefix traces, tests are
continuation-query pairs, and observing `u` at `(z, q)` means \(\rho(uz,q)\).
Its observation-generated extensional collapse (`ExtensionalCollapse.lean`) is
exactly the right-context quotient:

\[
\operatorname{Ext}(\text{prefix realization of }\rho)\;\simeq\;\Sigma^\ast/{\equiv_\rho}
\qquad\text{(`nerodeEquivCollapse`)}.
\]

So the object that survives the silent-extension obstruction of
`docs/IDENTIFIABILITY.md` is the Nerode quotient, and its tests separate its
states (`prefixSystem_collapse_extensional`).

The behavioral monoid acts on it by right concatenation,
\([w]\cdot[u]=[wu]\) (`Nerode.act`), the action respects products and the
unit (`Nerode.act_mul`, `Nerode.act_one`), and every state is reached from the
class of the empty trace (`Nerode.reach`). In automata language:
\(\Sigma^\ast/{\equiv_\rho}\) is the minimal state space and
\(B=\Sigma^\ast/{\approx_\rho}\) is its transition monoid. The Hankel table
of Section 7 has these states as rows.

## 5b. Invariance forces equations on behavior

Because \(\Gamma\) forgets order and repetition, the logical monoid is
commutative and idempotent (`LogicalSpace.mul_comm`, `LogicalSpace.mul_idem`,
from `logicalEquiv_comm` and `logicalEquiv_dup`). Hence whenever the canonical
path `F` exists, its image satisfies the same equations
(`recognitionMap_comm`, `recognitionMap_idem`), and at the level of traces:

\[
\equiv_{\mathsf L}\subseteq\approx_\rho
\;\Longrightarrow\;
uv\approx_\rho vu,\qquad ww\approx_\rho w,\qquad
u\approx_\rho \sigma(u)\ \text{for every permutation }\sigma .
\]

(`contextEquiv_comm_of_invariant`, `contextEquiv_dup_of_invariant`,
`contextEquiv_of_perm_of_invariant`.) These are not hypotheses about the model;
they are consequences of the single inclusion, and each is a falsifiable
prediction. The permutation experiments test the third, and a measured failure
of any of them refutes \(\equiv_{\mathsf L}\subseteq\approx_\rho\) on the
tested contexts.

## 5c. When a finite test family identifies the congruence

`RecognitionPaths/Identification.lean` answers the finite-versus-full question
at the set level. For a family of tests `T` (continuation-query pairs), write
\(\equiv_{\rho,T}\) for agreement on `T` (`RightEquivOn`). Say `T` is *direct*
when it contains every `([], q)`, and *closed* for \(\rho\) when

\[
u\equiv_{\rho,T}v
\;\Longrightarrow\;
ua\equiv_{\rho,T}va
\qquad\text{for every symbol }a
\]

(`Closed`; this is Angluin's consistency condition for an observation table).

**Identification theorem** (`rightEquiv_of_closed`, `closed_of_identifies`).
For a direct family `T`,

\[
\equiv_{\rho,T}\;=\;\equiv_\rho
\qquad\Longleftrightarrow\qquad
T\text{ is closed for }\rho .
\]

The criterion is constructive. If `T` is not closed, `refine_witness`
produces a pair \(u\equiv_{\rho,T}v\) and a test \((a z, q)\) with
\((z,q)\in T\) that separates them: the next column to add. For the
length-bounded families \(T_k=\{(z,q):|z|\le k\}\), one more level of
continuation is exactly one more symbol of prefix
(`boundedEquiv_succ_iff`), so as soon as \(T_k\) and \(T_{k+1}\) induce the
same relation, \(T_k\) is closed and identifies \(\equiv_\rho\)
(`rightEquiv_of_stable`). The two-sided statements for \(\approx_\rho\), with
closure under a symbol on either side, are `contextEquiv_of_closed₂` and
`closed₂_of_identifies`.

Two things are deliberately not claimed. The classical counting bound, that
\(n\) Nerode classes force stabilisation by \(k=n-1\), is standard but not
formalised (OPEN: it needs a pigeonhole argument). The \(\mathbb R\)-linear
refinement, in which the numerical rank of the Hankel table replaces the count
of classes, is the Fliess theory and is also not formalised.

## 5d. The observation table as a Chu space

Under the broadest reading of "geometry", the geometry that cannot be
removed from this project is the duality between points and tests: an
object is known through the outcomes of the tests applied to it. An
observation system \((S, T, e : S\times T\to O)\) is a Chu space, and a
Hankel table is one with rows \(S\) and columns \(T\).

`RecognitionPaths/Biextensional.lean` completes the collapse begun in
`ExtensionalCollapse.lean`. Tests are quotiented by equality of their state
profiles (`testSetoid`, `TestCollapse`), states by equality of their test
profiles (`Collapse`), and the observation descends to both
(`biextensionalCollapse`). In the result, tests separate states
(`biextensionalCollapse_extensional`) and states separate tests
(`biextensionalCollapse_coextensional`); collapsing the tests does not
change which states are identified (`profile_eq_iff_biext`); and a silent
extension has the same test collapse (`testCollapseSilentEquiv`).

The counts "distinct rows" and "distinct columns" reported for the Boolean
table in `proof-path-invariance` (Phase 3.2) are the sizes of these two
quotients. Metric geometry (Section 6) is a further choice layered on this
duality; the Boolean readout of Phase 3.2 removes that layer and keeps only
the duality, which is why the Recognition Factorization Theorem can be
checked there by exact equality.

## 5e. Specifications for constructed recognizers

`RecognitionPaths/Specification.lean` states what a recognizer built to
satisfy the theory must look like. A *theory-factoring* recognizer
\(\rho(w,q)=f(\Gamma(w),q)\) reads a trace only through its set of clauses;
it is invariant under permutation and repetition of any block in any
context by construction (`theoryRecognizer_contextEquiv_of_perm`,
`theoryRecognizer_contextEquiv_dup`), but nothing forces it to identify
two clause sets with the same consequences. The *ideal* recognizer
\(\rho(w,q)=\operatorname{Entails}(\Gamma(w),q)\) is logically invariant and
logically recoverable, so \(L\simeq B\) (`idealRecognizer_equiv`).

A model whose premise encoder is a set encoder realises the first
specification exactly. The distance between the two specifications, the
identification of consequence-equivalent clause sets, is what training
must supply, and it is measured on the same tables as before.

## 5f. The graded closure: budgets as grades

`RecognitionPaths/Graded.lean` replaces the closure operator by its finite
stages. One parallel round of forward chaining is `step`, and
\(T_k S=\) `rounds Γ k S` is the set of atoms known after \(k\) rounds from
\(S\). The family is an \(\mathbb N\)-graded monad on the poset of atom
sets:

* \(T_0=\mathrm{id}\) (`rounds_zero`) and \(T_j\circ T_k=T_{j+k}\)
  (`rounds_add`, the composition law);
* \(S\subseteq T_kS\subseteq T_{k+d}S\) (`rounds_extensive`, `rounds_le_add`),
  monotone in \(S\) and in the theory (`rounds_mono`, `rounds_mono_theory`);
* the limit \(T_\infty S=\bigcup_k T_kS\) is the least model containing
  \(S\) (`limit_models`), so semantic entailment is entailment at some
  finite grade (`entails_iff_exists_rounds`: soundness and completeness).

Only \(T_\infty\) is idempotent. Budget-\(k\) identity
\(u\approx_k w\) (`GradedEquiv k`) asks for the same answers within \(k\)
rounds for every query. It is blind to order and repetition at every grade
(`gradedEquiv_of_perm`, `gradedEquiv_dup`), identity at every grade implies
\(\equiv_L\) (`logicalEquiv_of_gradedEquiv`), and the converse fails at
any fixed grade: a trace and its extension by one clause are
budget-\(k\) identical exactly when the extension brings no query inside
the budget (`gradedEquiv_append_iff`, `not_gradedEquiv_append_iff`). For
a derivable clause the separation is transient
(`gradedEquiv_append_derivable_eventually`).

The budgeted recognizer `roundsRecognizer Atom k` answers by \(k\) rounds;
its behavioral identity is graded identity in every context
(`roundsRecognizer_contextEquiv_iff`). The composition law read on the
recognizer (`entailsK_presaturate`) says that pre-saturating the
hypotheses by \(j\) rounds and reading with budget \(k\) equals reading
with budget \(j+k\): a hint buys exactly its depth.

**Lax graded readers.** A learned budgeted reasoner need not compute
\(T_k\) exactly. `LaxGraded Γ s` packages a family of monotone operators
\(R_k\) with \(T_{k-s}S\subseteq R_kS\subseteq T_kS\). Slack \(0\) forces
\(R_k=T_k\) (`eq_rounds_of_slack_zero`); zero budget is the identity for
any slack (`zero_eq_id`); and composition inherits the sandwich with the
slack added: \(T_{j+k-2s}\subseteq R_j\circ R_k\subseteq T_{j+k}\)
(`comp_lower`, `comp_upper`, `comp_sandwich`). The reader found in RQ2c
has slack \(1\) on budgets \(k\ge1\); whether its self-composition has
slack \(2\), as the theorem allows, or less, is the RQ2g test.

This is the first place the theory names an algebraic object that a
constructed recognizer realises and that predicts, rather than describes,
which equal-meaning inputs it distinguishes. The RQ2 table of
`proof-path-invariance` is the empirical instance of
`not_gradedEquiv_append_iff`.

## 6. From exact equality to distance (not formalized)

Real logits are never exactly equal, so the practical object is the
behavioral distance

\[
d_\rho(u,v)=\sup_{x,z,q}d_O\bigl(\rho(xuz,q),\rho(xvz,q)\bigr),
\]

estimated on a finite test family `T` by
\(\widehat d_{\rho,T}(u,v)=\max_{(x,z,q)\in T}d_O(\cdot,\cdot)\). Restricting
to logically identical pairs gives the invariance defect

\[
\Delta_{\mathrm{inv}}(T)=\sup_{u\equiv_{\mathsf L}v}\widehat d_{\rho,T}(u,v),
\]

which is the correct generalization of the earlier "permutation effect". The
exact relations above are the \(\Delta_{\mathrm{inv}}=0\) case. The
quantitative (Lawvere-enriched) version is a later layer and is not formalized
here.

## 7. The observation the theorem asks for

The theorem compares two quotients of the same free monoid, so the experiment
that serves it is a rectangular observation table

\[
H_\rho(u,t)=\rho(u,t),\qquad t=(z,q),
\]

with prefix traces as rows and continuation-query tests as columns, replicated
under presentation controls. Its rows are the states of Section 5a restricted
to `T`, and Section 5c says exactly what the table can conclude: rows that
agree on `T` are \(\equiv_\rho\)-identical precisely when `T` is closed, and
a closure failure names the column that refines the table. Its structure is fixed in the
`proof-path-invariance` repository (`docs/PHASE3_HANKEL_DESIGN.md`).

## 8. What comes after, and only after

Once a behavioral congruence is observed, `B` is a monoid acting on the Nerode
states, and the operations and equations actually found in the data present
an algebraic theory
\(\mathbb T_\rho\). Its free/forgetful adjunction \(F_\rho\dashv U_\rho\)
yields the monad candidate \(T_\rho=U_\rho F_\rho\). The order is

\[
\text{observation}\to\text{equivalence}\to\text{quotient}\to
\text{operations and equations}\to\text{algebraic theory}\to\text{monad}.
\]

Of the later steps, one is now taken: the graded closure of §5f is the
monad candidate for budgeted recognizers, with its composition law as the
first equation. Whether any recognizer that was not built from it
satisfies that law is the empirical question that follows.
