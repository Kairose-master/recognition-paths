import RecognitionPaths.Horn
import RecognitionPaths.Factorization

namespace RecognitionPaths

universe u v w

/-- A recognizer maps an ordered premise trace and a query to an observation.
    The intended instance is a language model read at the answer position with
    `O = ℝ²` carrying both the YES and the NO logit. -/
structure Recognizer (Sym : Type u) (Q : Type v) (O : Type w) where
  observe : List Sym → Q → O

namespace Recognizer

variable {Sym : Type u} {Q : Type v} {O : Type w}

/-- Right-context behavioral identity `u ≡_ρ v`: no continuation and no query
    separates the two traces. -/
def RightEquiv (ρ : Recognizer Sym Q O) (u v : List Sym) : Prop :=
  ∀ (z : List Sym) (q : Q), ρ.observe (u ++ z) q = ρ.observe (v ++ z) q

/-- Two-sided context behavioral identity `u ≈_ρ v`: no surrounding context and
    no query separates the two traces.  This is the recognition congruence. -/
def ContextEquiv (ρ : Recognizer Sym Q O) (u v : List Sym) : Prop :=
  ∀ (x z : List Sym) (q : Q), ρ.observe (x ++ u ++ z) q = ρ.observe (x ++ v ++ z) q

/-- Behavioral identity relative to a chosen family of tests `(x, z, q)`.
    Experiments only ever observe one of these restrictions. -/
def ContextEquivOn (ρ : Recognizer Sym Q O)
    (T : List Sym → List Sym → Q → Prop) (u v : List Sym) : Prop :=
  ∀ (x z : List Sym) (q : Q), T x z q →
    ρ.observe (x ++ u ++ z) q = ρ.observe (x ++ v ++ z) q

theorem contextEquiv_refl (ρ : Recognizer Sym Q O) (u : List Sym) :
    ρ.ContextEquiv u u :=
  fun _ _ _ => rfl

theorem contextEquiv_symm {ρ : Recognizer Sym Q O} {u v : List Sym}
    (h : ρ.ContextEquiv u v) : ρ.ContextEquiv v u :=
  fun x z q => (h x z q).symm

theorem contextEquiv_trans {ρ : Recognizer Sym Q O} {u v t : List Sym}
    (h₁ : ρ.ContextEquiv u v) (h₂ : ρ.ContextEquiv v t) : ρ.ContextEquiv u t :=
  fun x z q => (h₁ x z q).trans (h₂ x z q)

/-- The setoid of two-sided behavioral identity. -/
def contextSetoid (ρ : Recognizer Sym Q O) : Setoid (List Sym) where
  r := ρ.ContextEquiv
  iseqv := ⟨ρ.contextEquiv_refl, contextEquiv_symm, contextEquiv_trans⟩

/-- The behavioral meaning space `B = Σ*/≈_ρ`, built from external behavior
    alone. -/
abbrev Behavior (ρ : Recognizer Sym Q O) := Quotient ρ.contextSetoid

/-- Two-sided identity implies right-context identity. -/
theorem rightEquiv_of_contextEquiv {ρ : Recognizer Sym Q O} {u v : List Sym}
    (h : ρ.ContextEquiv u v) : ρ.RightEquiv u v :=
  fun z q => h [] z q

/-- Full behavioral identity implies identity on every finite test family.
    The converse is the open identifiability question. -/
theorem contextEquivOn_of_contextEquiv {ρ : Recognizer Sym Q O}
    (T : List Sym → List Sym → Q → Prop) {u v : List Sym}
    (h : ρ.ContextEquiv u v) : ρ.ContextEquivOn T u v :=
  fun x z q _ => h x z q

/-- A larger test family induces a finer identity. -/
theorem contextEquivOn_mono {ρ : Recognizer Sym Q O}
    {T T' : List Sym → List Sym → Q → Prop}
    (hT : ∀ x z q, T x z q → T' x z q) {u v : List Sym}
    (h : ρ.ContextEquivOn T' u v) : ρ.ContextEquivOn T u v :=
  fun x z q hq => h x z q (hT x z q hq)

/-! ### `≈_ρ` is a congruence, so `B` is a monoid -/

theorem contextEquiv_append_left {ρ : Recognizer Sym Q O} {u v : List Sym}
    (x : List Sym) (h : ρ.ContextEquiv u v) : ρ.ContextEquiv (x ++ u) (x ++ v) := by
  intro y z q
  have := h (y ++ x) z q
  simpa [List.append_assoc] using this

theorem contextEquiv_append_right {ρ : Recognizer Sym Q O} {u v : List Sym}
    (z : List Sym) (h : ρ.ContextEquiv u v) : ρ.ContextEquiv (u ++ z) (v ++ z) := by
  intro x y q
  have := h x (z ++ y) q
  simpa [List.append_assoc] using this

theorem contextEquiv_append {ρ : Recognizer Sym Q O} {u u' v v' : List Sym}
    (hu : ρ.ContextEquiv u u') (hv : ρ.ContextEquiv v v') :
    ρ.ContextEquiv (u ++ v) (u' ++ v') :=
  contextEquiv_trans (contextEquiv_append_right v hu) (contextEquiv_append_left u' hv)

/-- Concatenation descends to behavioral classes. -/
def Behavior.mul (ρ : Recognizer Sym Q O) : ρ.Behavior → ρ.Behavior → ρ.Behavior :=
  Quotient.lift₂ (fun u v => Quotient.mk ρ.contextSetoid (u ++ v))
    fun _ _ _ _ hu hv => Quotient.sound (contextEquiv_append hu hv)

/-- The class of the empty trace. -/
def Behavior.one (ρ : Recognizer Sym Q O) : ρ.Behavior :=
  Quotient.mk ρ.contextSetoid []

@[simp]
theorem Behavior.mul_mk (ρ : Recognizer Sym Q O) (u v : List Sym) :
    Behavior.mul ρ (Quotient.mk ρ.contextSetoid u) (Quotient.mk ρ.contextSetoid v) =
      Quotient.mk ρ.contextSetoid (u ++ v) :=
  rfl

theorem Behavior.mul_assoc (ρ : Recognizer Sym Q O) (a b c : ρ.Behavior) :
    Behavior.mul ρ (Behavior.mul ρ a b) c = Behavior.mul ρ a (Behavior.mul ρ b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro u v t
  simp [List.append_assoc]

theorem Behavior.one_mul (ρ : Recognizer Sym Q O) (a : ρ.Behavior) :
    Behavior.mul ρ (Behavior.one ρ) a = a := by
  refine Quotient.inductionOn a ?_
  intro u
  rfl

theorem Behavior.mul_one (ρ : Recognizer Sym Q O) (a : ρ.Behavior) :
    Behavior.mul ρ a (Behavior.one ρ) = a := by
  refine Quotient.inductionOn a ?_
  intro u
  simp [Behavior.one]

end Recognizer

/-! ## The fixed small world: Horn traces read by a recognizer -/

namespace Horn

variable {Atom : Type u} {O : Type w}

/-- The logical meaning space is also a monoid: concatenation of traces
    descends to logical classes. -/
def LogicalSpace.mul : LogicalSpace Atom → LogicalSpace Atom → LogicalSpace Atom :=
  Quotient.lift₂ (fun u v => Quotient.mk (logicalSetoid Atom) (u ++ v))
    fun _ _ _ _ hu hv => Quotient.sound
      (logicalEquiv_trans (logicalEquiv_append_right _ hu) (logicalEquiv_append_left _ hv))

@[simp]
theorem LogicalSpace.mul_mk (u v : Trace Atom) :
    LogicalSpace.mul (Quotient.mk (logicalSetoid Atom) u) (Quotient.mk (logicalSetoid Atom) v) =
      Quotient.mk (logicalSetoid Atom) (u ++ v) :=
  rfl

/-- `≡_L ⊆ ≈_ρ`: the recognizer identifies logically identical traces. -/
def LogicallyInvariant (ρ : Recognizer (HornClause Atom) (Query Atom) O) : Prop :=
  Refines (logicalSetoid Atom) ρ.contextSetoid

/-- `≈_ρ ⊆ ≡_L`: logical identity is recoverable from behavior. -/
def LogicallyRecoverable (ρ : Recognizer (HornClause Atom) (Query Atom) O) : Prop :=
  Refines ρ.contextSetoid (logicalSetoid Atom)

/-- **Recognition Factorization Theorem** for the Horn world.  The recognizer
    identifies logically identical traces exactly when there is a unique map
    `F : L → B` sending each logical class to the behavioral class of any of
    its representatives. -/
theorem recognition_factorization
    (ρ : Recognizer (HornClause Atom) (Query Atom) O) :
    LogicallyInvariant ρ ↔
      ∃ F : LogicalSpace Atom → ρ.Behavior,
        (∀ w, F (Quotient.mk (logicalSetoid Atom) w) = Quotient.mk ρ.contextSetoid w) ∧
        ∀ G : LogicalSpace Atom → ρ.Behavior,
          (∀ w, G (Quotient.mk (logicalSetoid Atom) w) = Quotient.mk ρ.contextSetoid w) →
          G = F :=
  recognition_factorization_iff (logicalSetoid Atom) ρ.contextSetoid

/-- The canonical recognition path `F : L → B`, available under invariance. -/
def recognitionMap (ρ : Recognizer (HornClause Atom) (Query Atom) O)
    (h : LogicallyInvariant ρ) : LogicalSpace Atom → ρ.Behavior :=
  quotientMap (logicalSetoid Atom) ρ.contextSetoid h

@[simp]
theorem recognitionMap_mk (ρ : Recognizer (HornClause Atom) (Query Atom) O)
    (h : LogicallyInvariant ρ) (w : Trace Atom) :
    recognitionMap ρ h (Quotient.mk (logicalSetoid Atom) w) = Quotient.mk ρ.contextSetoid w :=
  rfl

/-- The canonical recognition path preserves concatenation: it is a monoid
    morphism from `L` to `B`. -/
theorem recognitionMap_mul (ρ : Recognizer (HornClause Atom) (Query Atom) O)
    (h : LogicallyInvariant ρ) (a b : LogicalSpace Atom) :
    recognitionMap ρ h (LogicalSpace.mul a b) =
      Recognizer.Behavior.mul ρ (recognitionMap ρ h a) (recognitionMap ρ h b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro u v
  rfl

/-- The reverse direction: logical identity is recoverable from behavior
    exactly when there is a unique representative-preserving `G : B → L`. -/
theorem recognition_recovery
    (ρ : Recognizer (HornClause Atom) (Query Atom) O) :
    LogicallyRecoverable ρ ↔
      ∃ G : ρ.Behavior → LogicalSpace Atom,
        (∀ w, G (Quotient.mk ρ.contextSetoid w) = Quotient.mk (logicalSetoid Atom) w) ∧
        ∀ G' : ρ.Behavior → LogicalSpace Atom,
          (∀ w, G' (Quotient.mk ρ.contextSetoid w) = Quotient.mk (logicalSetoid Atom) w) →
          G' = G :=
  recognition_factorization_iff ρ.contextSetoid (logicalSetoid Atom)

/-- Both directions together identify the two meaning spaces. -/
def recognitionEquiv (ρ : Recognizer (HornClause Atom) (Query Atom) O)
    (h₁ : LogicallyInvariant ρ) (h₂ : LogicallyRecoverable ρ) :
    LogicalSpace Atom ≃ ρ.Behavior :=
  quotientEquiv (logicalSetoid Atom) ρ.contextSetoid h₁ h₂

end Horn

end RecognitionPaths
