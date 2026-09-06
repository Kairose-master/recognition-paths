import RecognitionPaths.Recognition

/-!
# Specifications for constructed recognizers

Two reference recognizers fix what "invariance by construction" means.

* A **theory-factoring** recognizer reads a trace only through its set of
  clauses: `ρ(w, q) = f(Γ(w), q)`.  It is invariant under permutation and
  repetition by construction, but need not identify two different clause
  sets with the same consequences.
* The **ideal** recognizer reads a trace through its consequences:
  `ρ(w, q) = Entails(Γ(w), q)`.  It is logically invariant and logically
  recoverable, so `L ≃ B`.

A model whose premise encoder is a set encoder realises the first
specification exactly; whether training moves it toward the second is an
empirical question, measured on the same tables as before.
-/

namespace RecognitionPaths

namespace Horn

universe u w

variable {Atom : Type u} {O : Type w}

/-- A recognizer that factors through the theory (set of clauses). -/
def theoryRecognizer (f : Theory Atom → Query Atom → O) :
    Recognizer (HornClause Atom) (Query Atom) O where
  observe w q := f (theory w) q

/-- Theories of permuted traces coincide. -/
theorem theory_eq_of_perm {u w : Trace Atom} (p : List.Perm u w) :
    theory u = theory w := by
  funext c
  exact propext p.mem_iff

/-- The theory of a repeated trace is the theory of the trace. -/
theorem theory_append_self (w : Trace Atom) : theory (w ++ w) = theory w := by
  funext c
  apply propext
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h <;> exact h
  · intro h
    exact List.mem_append_left _ h

/-- Membership in a concatenation is membership in either part. -/
theorem theory_append (u w : Trace Atom) (c : HornClause Atom) :
    theory (u ++ w) c ↔ theory u c ∨ theory w c :=
  List.mem_append

/-- A theory-factoring recognizer is invariant under permutation of a
    block in any context. -/
theorem theoryRecognizer_contextEquiv_of_perm (f : Theory Atom → Query Atom → O)
    {u w : Trace Atom} (p : List.Perm u w) :
    (theoryRecognizer f).ContextEquiv u w := by
  intro x z q
  show f (theory (x ++ u ++ z)) q = f (theory (x ++ w ++ z)) q
  have : List.Perm (x ++ u ++ z) (x ++ w ++ z) :=
    List.Perm.append_right z (List.Perm.append_left x p)
  rw [theory_eq_of_perm this]

/-- A theory-factoring recognizer is invariant under repetition of a block
    in any context. -/
theorem theoryRecognizer_contextEquiv_dup (f : Theory Atom → Query Atom → O)
    (w : Trace Atom) :
    (theoryRecognizer f).ContextEquiv (w ++ w) w := by
  intro x z q
  have h : theory (x ++ (w ++ w) ++ z) = theory (x ++ w ++ z) := by
    funext c
    simp [theory, List.mem_append]
  show f (theory (x ++ (w ++ w) ++ z)) q = f (theory (x ++ w ++ z)) q
  rw [h]

/-- The ideal recognizer answers exactly the entailment question.  Its
    observation space is `Prop`. -/
def idealRecognizer (Atom : Type u) :
    Recognizer (HornClause Atom) (Query Atom) Prop where
  observe w q := Entails (theory w) q

/-- The ideal recognizer identifies logically identical traces. -/
theorem idealRecognizer_invariant (Atom : Type u) :
    LogicallyInvariant (idealRecognizer Atom) := by
  intro u w h x z q
  show Entails (theory (x ++ u ++ z)) q = Entails (theory (x ++ w ++ z)) q
  exact propext (logicalEquiv_congr x z h q)

/-- Logical identity is recoverable from the ideal recognizer. -/
theorem idealRecognizer_recoverable (Atom : Type u) :
    LogicallyRecoverable (idealRecognizer Atom) := by
  intro u w h q
  have := h [] [] q
  simpa [idealRecognizer] using Iff.of_eq this

/-- For the ideal recognizer the logical and behavioral meaning spaces
    coincide. -/
def idealRecognizer_equiv (Atom : Type u) :
    LogicalSpace Atom ≃ (idealRecognizer Atom).Behavior :=
  recognitionEquiv (idealRecognizer Atom)
    (idealRecognizer_invariant Atom) (idealRecognizer_recoverable Atom)

end Horn

end RecognitionPaths
