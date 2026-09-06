import RecognitionPaths.Specification

/-!
# The graded closure: budgets as grades

Forward chaining for `k` parallel rounds is an operator `T_k` on atom sets.
The family `(T_k)` is an `ℕ`-graded monad on the poset of atom sets:

* `T_0 = id`;
* `T_j ∘ T_k = T_{j+k}`  (composition law);
* `S ⊆ T_k S ⊆ T_{k+1} S`, and `T_k` is monotone in `S` and in the theory;
* the limit `T_∞ S = ⋃_k T_k S` is the closure operator whose kernel is
  logical identity `≡_L` (soundness and completeness).

Only the limit is idempotent.  A recognizer that reads a trace through
`T_k` for a fixed budget `k` has the graded behavioral identity `≈_k`
(`GradedEquiv k`): it is invariant under permutation and repetition, and
it identifies a trace with a redundant extension exactly when the
extension brings no query inside the budget (`gradedEquiv_append_iff`).
This is the statement tested in RQ2.
-/

namespace RecognitionPaths

namespace Horn

universe u

variable {Atom : Type u}

/-- Atom sets, as predicates. -/
abbrev AtomSet (Atom : Type u) := Atom → Prop

/-- Inclusion of atom sets. -/
def Sub (S T : AtomSet Atom) : Prop := ∀ a, S a → T a

theorem Sub.refl (S : AtomSet Atom) : Sub S S := fun _ h => h

theorem Sub.trans {S T U : AtomSet Atom} (h₁ : Sub S T) (h₂ : Sub T U) : Sub S U :=
  fun a h => h₂ a (h₁ a h)

theorem holds_mono {S T : AtomSet Atom} (h : Sub S T) (as : List Atom)
    (hs : Holds S as) : Holds T as :=
  fun a ha => h a (hs a ha)

/-! ### One round, `k` rounds -/

/-- One parallel round of forward chaining: every clause whose body is known
    fires. -/
def step (Γ : Theory Atom) (S : AtomSet Atom) : AtomSet Atom :=
  fun a => S a ∨ ∃ c, Γ c ∧ Holds S c.body ∧ a ∈ c.head

/-- `rounds Γ k S = T_k S`: the atoms known after `k` rounds from `S`. -/
def rounds (Γ : Theory Atom) : Nat → AtomSet Atom → AtomSet Atom
  | 0, S => S
  | k + 1, S => step Γ (rounds Γ k S)

@[simp] theorem rounds_zero (Γ : Theory Atom) (S : AtomSet Atom) :
    rounds Γ 0 S = S := rfl

@[simp] theorem rounds_succ (Γ : Theory Atom) (k : Nat) (S : AtomSet Atom) :
    rounds Γ (k + 1) S = step Γ (rounds Γ k S) := rfl

/-- **Composition law** `T_j ∘ T_k = T_{j+k}`: the grades add. -/
theorem rounds_add (Γ : Theory Atom) (j k : Nat) (S : AtomSet Atom) :
    rounds Γ j (rounds Γ k S) = rounds Γ (j + k) S := by
  induction j with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
    show step Γ (rounds Γ j (rounds Γ k S)) = rounds Γ (j + 1 + k) S
    rw [ih, Nat.add_right_comm]
    rfl

/-- `T_k` is extensive. -/
theorem rounds_extensive (Γ : Theory Atom) (k : Nat) (S : AtomSet Atom) :
    Sub S (rounds Γ k S) := by
  induction k with
  | zero => exact Sub.refl S
  | succ k ih => exact fun a h => Or.inl (ih a h)

/-- The grades are nested: `T_k S ⊆ T_{k+d} S`. -/
theorem rounds_le_add (Γ : Theory Atom) (k d : Nat) (S : AtomSet Atom) :
    Sub (rounds Γ k S) (rounds Γ (k + d) S) := by
  induction d with
  | zero => exact Sub.refl _
  | succ d ih => exact fun a h => Or.inl (ih a h)

theorem step_mono (Γ : Theory Atom) {S T : AtomSet Atom} (h : Sub S T) :
    Sub (step Γ S) (step Γ T) := by
  intro a ha
  rcases ha with ha | ⟨c, hc, hb, hh⟩
  · exact Or.inl (h a ha)
  · exact Or.inr ⟨c, hc, holds_mono h _ hb, hh⟩

/-- `T_k` is monotone in the atom set. -/
theorem rounds_mono (Γ : Theory Atom) (k : Nat) {S T : AtomSet Atom} (h : Sub S T) :
    Sub (rounds Γ k S) (rounds Γ k T) := by
  induction k with
  | zero => exact h
  | succ k ih => exact step_mono Γ ih

/-- `T_k` is monotone in the theory. -/
theorem rounds_mono_theory {Γ Δ : Theory Atom} (h : ∀ c, Γ c → Δ c) (k : Nat)
    (S : AtomSet Atom) : Sub (rounds Γ k S) (rounds Δ k S) := by
  induction k with
  | zero => exact Sub.refl S
  | succ k ih =>
    intro a ha
    rcases ha with ha | ⟨c, hc, hb, hh⟩
    · exact Or.inl (ih a ha)
    · exact Or.inr ⟨c, h c hc, holds_mono ih _ hb, hh⟩

/-! ### Soundness and completeness of the limit -/

/-- Every atom derived in `k` rounds holds in every model of `Γ` that makes
    `S` true. -/
theorem rounds_sound {Γ : Theory Atom} {v : Valuation Atom} (hv : Models v Γ)
    {S : AtomSet Atom} (hS : Sub S v) (k : Nat) : Sub (rounds Γ k S) v := by
  induction k with
  | zero => exact hS
  | succ k ih =>
    intro a ha
    rcases ha with ha | ⟨c, hc, hb, hh⟩
    · exact ih a ha
    · exact hv c hc (holds_mono ih _ hb) a hh

/-- The hypotheses of a query, as an atom set. -/
def hypSet (q : Query Atom) : AtomSet Atom := fun a => a ∈ q.hyps

/-- **Graded entailment**: the goal is derived from the hypotheses within
    `k` rounds. -/
def EntailsK (Γ : Theory Atom) (k : Nat) (q : Query Atom) : Prop :=
  rounds Γ k (hypSet q) q.goal

theorem entails_of_entailsK {Γ : Theory Atom} {k : Nat} {q : Query Atom}
    (h : EntailsK Γ k q) : Entails Γ q :=
  fun _ hv hh => rounds_sound hv (fun a ha => hh a ha) k q.goal h

theorem entailsK_le_add {Γ : Theory Atom} {k : Nat} {q : Query Atom} (d : Nat)
    (h : EntailsK Γ k q) : EntailsK Γ (k + d) q :=
  rounds_le_add Γ k d _ q.goal h

/-- The limit `T_∞ S = ⋃_k T_k S`. -/
def limit (Γ : Theory Atom) (S : AtomSet Atom) : AtomSet Atom :=
  fun a => ∃ k, rounds Γ k S a

/-- A finite list of atoms in the limit is already in some finite stage. -/
theorem holds_limit_bound {Γ : Theory Atom} {S : AtomSet Atom} :
    ∀ as : List Atom, Holds (limit Γ S) as → ∃ K, Holds (rounds Γ K S) as
  | [], _ => ⟨0, fun a ha => by simp at ha⟩
  | a :: as, h => by
    obtain ⟨k, hk⟩ := h a (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨K, hK⟩ := holds_limit_bound as (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))
    refine ⟨k + K, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with hba | hb
    · subst hba
      exact rounds_le_add Γ k K S b hk
    · rw [Nat.add_comm]
      exact rounds_le_add Γ K k S b (hK b hb)

/-- The limit is a model of the theory: the least model containing `S`. -/
theorem limit_models (Γ : Theory Atom) (S : AtomSet Atom) : Models (limit Γ S) Γ := by
  intro c hc hb a ha
  obtain ⟨K, hK⟩ := holds_limit_bound c.body hb
  exact ⟨K + 1, Or.inr ⟨c, hc, hK, ha⟩⟩

/-- **Completeness of the graded family**: semantic entailment is entailment
    at some finite grade.  The kernel of `T_∞` is logical identity. -/
theorem entails_iff_exists_rounds (Γ : Theory Atom) (q : Query Atom) :
    Entails Γ q ↔ ∃ k, EntailsK Γ k q := by
  constructor
  · intro h
    exact h (limit Γ (hypSet q)) (limit_models Γ _) (fun a ha => ⟨0, ha⟩)
  · intro ⟨_, hk⟩
    exact entails_of_entailsK hk

/-! ### Graded behavioral identity -/

/-- `u ≈_k w`: the same answers within budget `k` for every query. -/
def GradedEquiv (k : Nat) (u w : Trace Atom) : Prop :=
  ∀ q : Query Atom, EntailsK (theory u) k q ↔ EntailsK (theory w) k q

theorem gradedEquiv_refl (k : Nat) (u : Trace Atom) : GradedEquiv k u u :=
  fun _ => Iff.rfl

theorem gradedEquiv_symm {k : Nat} {u w : Trace Atom} (h : GradedEquiv k u w) :
    GradedEquiv k w u :=
  fun q => (h q).symm

theorem gradedEquiv_trans {k : Nat} {u w x : Trace Atom}
    (h₁ : GradedEquiv k u w) (h₂ : GradedEquiv k w x) : GradedEquiv k u x :=
  fun q => (h₁ q).trans (h₂ q)

/-- The setoid of budget-`k` identity. -/
def gradedSetoid (Atom : Type u) (k : Nat) : Setoid (Trace Atom) where
  r := GradedEquiv k
  iseqv := ⟨gradedEquiv_refl k, gradedEquiv_symm, gradedEquiv_trans⟩

/-- Budget-`k` identity is blind to order and repetition, at every grade. -/
theorem gradedEquiv_of_perm {u w : Trace Atom} (p : List.Perm u w) (k : Nat) :
    GradedEquiv k u w := by
  intro q
  rw [theory_eq_of_perm p]

theorem gradedEquiv_dup (w : Trace Atom) (k : Nat) : GradedEquiv k (w ++ w) w := by
  intro q
  rw [theory_append_self]

/-- Logical identity is identity at every grade in the limit. -/
theorem logicalEquiv_iff_limit (u w : Trace Atom) :
    LogicalEquiv u w ↔
      ∀ q : Query Atom, (∃ k, EntailsK (theory u) k q) ↔ (∃ k, EntailsK (theory w) k q) := by
  constructor
  · intro h q
    rw [← entails_iff_exists_rounds, ← entails_iff_exists_rounds]
    exact h q
  · intro h q
    rw [entails_iff_exists_rounds, entails_iff_exists_rounds]
    exact h q

/-- Identity at every finite grade implies logical identity.  The converse
    fails: RQ2 exhibits logically identical traces separated at a finite
    grade (`gradedEquiv_append_iff`). -/
theorem logicalEquiv_of_gradedEquiv {u w : Trace Atom}
    (h : ∀ k, GradedEquiv k u w) : LogicalEquiv u w := by
  rw [logicalEquiv_iff_limit]
  intro q
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k, (h k q).mp hk⟩
  · intro ⟨k, hk⟩
    exact ⟨k, (h k q).mpr hk⟩

/-! ### Extensions and the budget -/

/-- Adding clauses can only add derivations within a fixed budget. -/
theorem entailsK_mono_append {u : Trace Atom} (z : Trace Atom) {k : Nat}
    {q : Query Atom} (h : EntailsK (theory u) k q) : EntailsK (theory (u ++ z)) k q :=
  rounds_mono_theory (fun _ hc => List.mem_append_left z hc) k _ q.goal h

/-- **The RQ2 theorem.**  A trace and its extension by a clause are
    budget-`k` identical exactly when the extension brings no query inside
    the budget: every query answered within `k` rounds after the extension
    was already answered within `k` rounds before it. -/
theorem gradedEquiv_append_iff (k : Nat) (w : Trace Atom) (c : HornClause Atom) :
    GradedEquiv k w (w ++ [c]) ↔
      ∀ q : Query Atom, EntailsK (theory (w ++ [c])) k q → EntailsK (theory w) k q := by
  constructor
  · intro h q hq
    exact (h q).mpr hq
  · intro h q
    exact ⟨entailsK_mono_append [c], h q⟩

/-- Separation at grade `k` is witnessed by a query whose derivation the
    extension moves across the budget. -/
theorem not_gradedEquiv_append_iff (k : Nat) (w : Trace Atom) (c : HornClause Atom) :
    ¬ GradedEquiv k w (w ++ [c]) ↔
      ∃ q : Query Atom, EntailsK (theory (w ++ [c])) k q ∧ ¬ EntailsK (theory w) k q := by
  rw [gradedEquiv_append_iff]
  constructor
  · intro h
    exact Classical.byContradiction fun hne =>
      h fun q hq => Classical.byContradiction fun hw => hne ⟨q, hq, hw⟩
  · intro ⟨q, hq, hw⟩ h
    exact hw (h q hq)

/-- For a derivable clause the separation is transient: for every query
    there is a grade beyond which the trace and its extension agree. -/
theorem gradedEquiv_append_derivable_eventually {w : Trace Atom} {c : HornClause Atom}
    (hd : Derivable w c) (q : Query Atom) :
    ∃ K, ∀ d, (EntailsK (theory (w ++ [c])) (K + d) q ↔ EntailsK (theory w) (K + d) q) := by
  by_cases h : Entails (theory w) q
  · obtain ⟨K, hK⟩ := (entails_iff_exists_rounds _ _).mp h
    exact ⟨K, fun d => ⟨fun _ => entailsK_le_add d hK, entailsK_mono_append [c]⟩⟩
  · refine ⟨0, fun d => ⟨fun h' => ?_, entailsK_mono_append [c]⟩⟩
    exact absurd ((logicalEquiv_append_derivable hd q).mp (entails_of_entailsK h')) h

/-! ### The budgeted recognizer -/

/-- The recognizer that answers by `k` rounds of forward chaining. -/
def roundsRecognizer (Atom : Type u) (k : Nat) :
    Recognizer (HornClause Atom) (Query Atom) Prop :=
  theoryRecognizer fun Γ q => EntailsK Γ k q

/-- Its behavioral identity is graded identity in every context. -/
theorem roundsRecognizer_contextEquiv_iff (k : Nat) (u w : Trace Atom) :
    (roundsRecognizer Atom k).ContextEquiv u w ↔
      ∀ x z : Trace Atom, GradedEquiv k (x ++ u ++ z) (x ++ w ++ z) := by
  constructor
  · intro h x z q
    exact Iff.of_eq (h x z q)
  · intro h x z q
    exact propext (h x z q)

/-- Permutation and repetition are invisible to the budgeted recognizer. -/
theorem roundsRecognizer_contextEquiv_of_perm (k : Nat) {u w : Trace Atom}
    (p : List.Perm u w) : (roundsRecognizer Atom k).ContextEquiv u w :=
  theoryRecognizer_contextEquiv_of_perm _ p

theorem roundsRecognizer_contextEquiv_dup (k : Nat) (w : Trace Atom) :
    (roundsRecognizer Atom k).ContextEquiv (w ++ w) w :=
  theoryRecognizer_contextEquiv_dup _ w

/-- **Composition law for the recognizer**: answering from the `j`-round
    consequences of the hypotheses with budget `k` is answering from the
    hypotheses with budget `j + k`.  Pre-saturating the input by `j` rounds
    buys exactly `j` rounds of budget. -/
theorem entailsK_presaturate (Γ : Theory Atom) (j k : Nat) (S : AtomSet Atom) (g : Atom) :
    rounds Γ k (rounds Γ j S) g ↔ rounds Γ (j + k) S g := by
  rw [rounds_add, Nat.add_comm]

end Horn

end RecognitionPaths
