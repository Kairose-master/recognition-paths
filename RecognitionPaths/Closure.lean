import RecognitionPaths.Graded

/-!
# The closure monad on theories

`Cl Γ` is the set of clauses derivable from `Γ`.  On the poset of theories
under inclusion it is a closure operator, i.e. a monad: extensive,
monotone, idempotent.  Its fixed points are the closed theories, and
logical identity of traces is equality of closures
(`logicalEquiv_iff_cl_eq`): the logical meaning space `L` is the set of
algebras of this monad.  The graded closure of `Graded.lean` is its
filtration by rounds; `Cl` itself is the `∞`-stage.
-/

namespace RecognitionPaths

namespace Horn

universe u

variable {Atom : Type u}

/-- A clause is derivable from a theory when each head atom is entailed by
    the body. -/
def DerivableT (Γ : Theory Atom) (c : HornClause Atom) : Prop :=
  ∀ a, a ∈ c.head → Entails Γ ⟨c.body, a⟩

/-- The closure of a theory: all clauses derivable from it. -/
def Cl (Γ : Theory Atom) : Theory Atom := DerivableT Γ

/-- Inclusion of theories. -/
def SubT (Γ Δ : Theory Atom) : Prop := ∀ c, Γ c → Δ c

theorem entails_of_mem {Γ : Theory Atom} {c : HornClause Atom} (hc : Γ c) {a : Atom}
    (ha : a ∈ c.head) : Entails Γ ⟨c.body, a⟩ :=
  fun _ hv hb => hv c hc hb a ha

/-- `Γ ⊆ Cl Γ`. -/
theorem cl_extensive (Γ : Theory Atom) : SubT Γ (Cl Γ) :=
  fun _ hc _ ha => entails_of_mem hc ha

theorem entails_mono {Γ Δ : Theory Atom} (h : SubT Γ Δ) {q : Query Atom}
    (hq : Entails Γ q) : Entails Δ q :=
  fun v hv hh => hq v (fun c hc => hv c (h c hc)) hh

/-- `Cl` is monotone. -/
theorem cl_mono {Γ Δ : Theory Atom} (h : SubT Γ Δ) : SubT (Cl Γ) (Cl Δ) :=
  fun _ hc a ha => entails_mono h (hc a ha)

/-- Every model of `Γ` is a model of `Cl Γ`. -/
theorem models_cl {Γ : Theory Atom} {v : Valuation Atom} (hv : Models v Γ) : Models v (Cl Γ) :=
  fun _ hc hb a ha => hc a ha v hv hb

/-- Entailment from the closure is entailment from the theory. -/
theorem entails_cl_iff (Γ : Theory Atom) (q : Query Atom) : Entails (Cl Γ) q ↔ Entails Γ q :=
  ⟨fun h v hv hh => h v (models_cl hv) hh, entails_mono (cl_extensive Γ)⟩

/-- `Cl` is idempotent: `Cl (Cl Γ) ⊆ Cl Γ`. -/
theorem cl_idem (Γ : Theory Atom) : SubT (Cl (Cl Γ)) (Cl Γ) :=
  fun _ hc a ha => (entails_cl_iff Γ _).mp (hc a ha)

theorem cl_cl (Γ : Theory Atom) : Cl (Cl Γ) = Cl Γ := by
  funext c
  exact propext ⟨cl_idem Γ c, cl_extensive (Cl Γ) c⟩

/-- A theory is closed when it is its own closure. -/
def Closed (Γ : Theory Atom) : Prop := Cl Γ = Γ

theorem closed_cl (Γ : Theory Atom) : Closed (Cl Γ) := cl_cl Γ

/-- **Logical identity is equality of closures.**  The logical meaning
    space is the set of closed theories, the algebras of the closure
    monad. -/
theorem logicalEquiv_iff_cl_eq (u w : Trace Atom) :
    LogicalEquiv u w ↔ Cl (theory u) = Cl (theory w) := by
  constructor
  · intro h
    funext c
    apply propext
    constructor
    · intro hc a ha
      exact (h ⟨c.body, a⟩).mp (hc a ha)
    · intro hc a ha
      exact (h ⟨c.body, a⟩).mpr (hc a ha)
  · intro h q
    rw [← entails_cl_iff (theory u), ← entails_cl_iff (theory w), h]

/-- The graded closure is a filtration of `Cl`: a single-atom clause is in
    `Cl Γ` iff its head is reached from its body at some grade. -/
theorem mem_cl_iff_exists_rounds (Γ : Theory Atom) (x y : Atom) :
    Cl Γ ⟨[x], [y]⟩ ↔ ∃ k, rounds Γ k (fun a => a ∈ [x]) y := by
  constructor
  · intro h
    exact (entails_iff_exists_rounds Γ ⟨[x], y⟩).mp (h y (List.mem_singleton.mpr rfl))
  · intro h a ha
    have : a = y := List.mem_singleton.mp ha
    subst this
    exact (entails_iff_exists_rounds Γ ⟨[x], a⟩).mpr h

end Horn

end RecognitionPaths
