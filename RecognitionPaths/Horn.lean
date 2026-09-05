namespace RecognitionPaths

universe u

/-- A Horn clause `a₁ ∧ ⋯ ∧ aₘ → b₁ ∧ ⋯ ∧ bₙ` over a type of atoms.  Both the
    antecedent and the consequent are conjunctions of atoms, so the signature
    contains `A → B`, `A ∧ B → C`, and `A → B ∧ C`.  An empty body is a fact. -/
structure HornClause (Atom : Type u) where
  body : List Atom
  head : List Atom

/-- A query asks whether the atoms `hyps`, together with the theory, force the
    atom `goal`. -/
structure Query (Atom : Type u) where
  hyps : List Atom
  goal : Atom

/-- An ordered premise trace: a word over the Horn signature. -/
abbrev Trace (Atom : Type u) := List (HornClause Atom)

namespace Horn

variable {Atom : Type u}

/-- A theory is a set of clauses.  Sets are represented as predicates. -/
abbrev Theory (Atom : Type u) := HornClause Atom → Prop

/-- `Γ w`: forget the order of a trace and keep only its clauses. -/
def theory (w : Trace Atom) : Theory Atom :=
  fun c => c ∈ w

/-- A valuation assigns a truth value to each atom. -/
abbrev Valuation (Atom : Type u) := Atom → Prop

/-- A valuation makes every atom in a list true. -/
def Holds (v : Valuation Atom) (as : List Atom) : Prop :=
  ∀ a, a ∈ as → v a

/-- A valuation satisfies a clause when the body forces the head. -/
def Satisfies (v : Valuation Atom) (c : HornClause Atom) : Prop :=
  Holds v c.body → Holds v c.head

/-- A model of a theory satisfies each of its clauses. -/
def Models (v : Valuation Atom) (Γ : Theory Atom) : Prop :=
  ∀ c, Γ c → Satisfies v c

/-- Semantic Horn entailment: every model of `Γ` that makes the hypotheses
    true makes the goal true. -/
def Entails (Γ : Theory Atom) (q : Query Atom) : Prop :=
  ∀ v : Valuation Atom, Models v Γ → Holds v q.hyps → v q.goal

/-- Theory-level logical identity of traces: the same consequences for every
    query, not merely for the query used in one experiment. -/
def LogicalEquiv (u w : Trace Atom) : Prop :=
  ∀ q : Query Atom, Entails (theory u) q ↔ Entails (theory w) q

theorem logicalEquiv_refl (u : Trace Atom) : LogicalEquiv u u :=
  fun _ => Iff.rfl

theorem logicalEquiv_symm {u w : Trace Atom} (h : LogicalEquiv u w) :
    LogicalEquiv w u :=
  fun q => (h q).symm

theorem logicalEquiv_trans {u w x : Trace Atom}
    (h₁ : LogicalEquiv u w) (h₂ : LogicalEquiv w x) : LogicalEquiv u x :=
  fun q => (h₁ q).trans (h₂ q)

/-- The setoid of theory-level logical identity. -/
def logicalSetoid (Atom : Type u) : Setoid (Trace Atom) where
  r := LogicalEquiv
  iseqv := ⟨logicalEquiv_refl, logicalEquiv_symm, logicalEquiv_trans⟩

/-- The logical meaning space `L = Σ*/≡_L`. -/
abbrev LogicalSpace (Atom : Type u) := Quotient (logicalSetoid Atom)

/-! ### Order is logically invisible -/

theorem models_of_perm {v : Valuation Atom} {u w : Trace Atom}
    (p : List.Perm u w) (h : Models v (theory u)) : Models v (theory w) :=
  fun c hc => h c (p.mem_iff.mpr hc)

/-- Permuting a premise trace does not change any logical consequence.  This
    is the formal content of "same formal problem" for the S3 experiments. -/
theorem logicalEquiv_of_perm {u w : Trace Atom} (p : List.Perm u w) :
    LogicalEquiv u w := by
  intro q
  constructor
  · intro h v hv hh
    exact h v (models_of_perm p.symm hv) hh
  · intro h v hv hh
    exact h v (models_of_perm p hv) hh

/-- Concatenation of traces is logically commutative. -/
theorem logicalEquiv_comm (u w : Trace Atom) : LogicalEquiv (u ++ w) (w ++ u) :=
  logicalEquiv_of_perm List.perm_append_comm

theorem models_of_dup {v : Valuation Atom} {w : Trace Atom}
    (h : Models v (theory w)) : Models v (theory (w ++ w)) :=
  fun c hc => h c (by
    rcases List.mem_append.mp hc with hc | hc <;> exact hc)

/-- Repeating a trace adds no logical content: concatenation is logically
    idempotent. -/
theorem logicalEquiv_dup (w : Trace Atom) : LogicalEquiv (w ++ w) w := by
  intro q
  constructor
  · intro h v hv hh
    exact h v (models_of_dup hv) hh
  · intro h v hv hh
    exact h v (fun c hc => hv c (List.mem_append_left _ hc)) hh

/-! ### Logical identity is a congruence for concatenation

Two traces with the same consequences have the same models: each clause of
`w` is itself a consequence of `w`, hence of `u`.  Consequences of a common
extension therefore agree as well. -/

/-- Every clause of a theory is one of its consequences, atom by atom. -/
theorem entails_clause_atom {w : Trace Atom} {c : HornClause Atom}
    (hc : c ∈ w) {a : Atom} (ha : a ∈ c.head) :
    Entails (theory w) ⟨c.body, a⟩ :=
  fun _ hv hb => hv c hc hb a ha

theorem models_of_logicalEquiv {u w : Trace Atom} (h : LogicalEquiv u w)
    {v : Valuation Atom} (hv : Models v (theory u)) : Models v (theory w) := by
  intro c hc hb a ha
  exact (h ⟨c.body, a⟩).mpr (entails_clause_atom hc ha) v hv hb

theorem models_append {v : Valuation Atom} {u w : Trace Atom} :
    Models v (theory (u ++ w)) ↔ Models v (theory u) ∧ Models v (theory w) := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩
  · intro h c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.1 c hc
    · exact h.2 c hc

theorem logicalEquiv_append_left {u w : Trace Atom} (x : Trace Atom)
    (h : LogicalEquiv u w) : LogicalEquiv (x ++ u) (x ++ w) := by
  intro q
  constructor
  · intro hu v hv hh
    have hv' := models_append.mp hv
    exact hu v (models_append.mpr ⟨hv'.1, models_of_logicalEquiv (logicalEquiv_symm h) hv'.2⟩) hh
  · intro hw v hv hh
    have hv' := models_append.mp hv
    exact hw v (models_append.mpr ⟨hv'.1, models_of_logicalEquiv h hv'.2⟩) hh

theorem logicalEquiv_append_right {u w : Trace Atom} (z : Trace Atom)
    (h : LogicalEquiv u w) : LogicalEquiv (u ++ z) (w ++ z) := by
  intro q
  constructor
  · intro hu v hv hh
    have hv' := models_append.mp hv
    exact hu v (models_append.mpr ⟨models_of_logicalEquiv (logicalEquiv_symm h) hv'.1, hv'.2⟩) hh
  · intro hw v hv hh
    have hv' := models_append.mp hv
    exact hw v (models_append.mpr ⟨models_of_logicalEquiv h hv'.1, hv'.2⟩) hh

/-- Logical identity is a two-sided congruence on the free monoid of traces. -/
theorem logicalEquiv_congr {u w : Trace Atom} (x z : Trace Atom)
    (h : LogicalEquiv u w) : LogicalEquiv (x ++ u ++ z) (x ++ w ++ z) :=
  logicalEquiv_append_right z (logicalEquiv_append_left x h)

end Horn

end RecognitionPaths
