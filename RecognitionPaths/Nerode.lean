import RecognitionPaths.Recognition
import RecognitionPaths.ExtensionalCollapse

/-!
# The Nerode quotient is the extensional collapse of the prefix realization

A recognizer `ρ : Σ* × Q → O` has an obvious "raw" realization: states are
prefix traces, tests are continuation-query pairs, and observing a state means
appending the continuation and asking the query.  This file proves that the
observation-generated collapse of that realization (`ExtensionalCollapse.lean`)
is exactly the right-context quotient `Σ*/≡_ρ` (`Recognition.lean`), and that
the behavioral monoid `B = Σ*/≈_ρ` acts on it by right concatenation.

So the two halves of the library meet: the identifiable state object of the
identifiability programme is the Nerode quotient, and the syntactic monoid
acts on it as the transition monoid.
-/

namespace RecognitionPaths

universe u v w

namespace Recognizer

variable {Sym : Type u} {Q : Type v} {O : Type w}

/-- The prefix realization: raw states are prefix traces, tests are
    continuation-query pairs. -/
def prefixSystem (ρ : Recognizer Sym Q O) :
    ObservationSystem.{u, max u v, w} (List Sym × Q) O where
  State := List Sym
  observe u t := ρ.observe (u ++ t.1) t.2

/-- Right-context identity is precisely observational identity in the prefix
    realization. -/
theorem rightEquiv_iff_profile_eq (ρ : Recognizer Sym Q O) (u v : List Sym) :
    ρ.RightEquiv u v ↔ ρ.prefixSystem.profile u = ρ.prefixSystem.profile v := by
  constructor
  · intro h
    funext t
    exact h t.1 t.2
  · intro h z q
    exact congrFun h (z, q)

theorem rightEquiv_refl (ρ : Recognizer Sym Q O) (u : List Sym) : ρ.RightEquiv u u :=
  fun _ _ => rfl

theorem rightEquiv_symm {ρ : Recognizer Sym Q O} {u v : List Sym}
    (h : ρ.RightEquiv u v) : ρ.RightEquiv v u :=
  fun z q => (h z q).symm

theorem rightEquiv_trans {ρ : Recognizer Sym Q O} {u v t : List Sym}
    (h₁ : ρ.RightEquiv u v) (h₂ : ρ.RightEquiv v t) : ρ.RightEquiv u t :=
  fun z q => (h₁ z q).trans (h₂ z q)

/-- The setoid of right-context identity (the Nerode relation of `ρ`). -/
def rightSetoid (ρ : Recognizer Sym Q O) : Setoid (List Sym) where
  r := ρ.RightEquiv
  iseqv := ⟨ρ.rightEquiv_refl, rightEquiv_symm, rightEquiv_trans⟩

/-- The Nerode quotient `Σ*/≡_ρ`: the observation-generated state space. -/
abbrev Nerode (ρ : Recognizer Sym Q O) := Quotient ρ.rightSetoid

/-- The Nerode quotient is the extensional collapse of the prefix realization.
    Both quotients are taken on the same carrier `Σ*`, and their relations
    coincide, so the identity on representatives descends in both directions. -/
def nerodeEquivCollapse (ρ : Recognizer Sym Q O) :
    ρ.Nerode ≃ ρ.prefixSystem.Collapse where
  toFun := Quotient.lift (fun u => Quotient.mk ρ.prefixSystem.observationalSetoid u)
    fun _ _ h => Quotient.sound ((ρ.rightEquiv_iff_profile_eq _ _).mp h)
  invFun := Quotient.lift (fun u => Quotient.mk ρ.rightSetoid u)
    fun _ _ h => Quotient.sound ((ρ.rightEquiv_iff_profile_eq _ _).mpr h)
  left_inv := by
    intro s
    refine Quotient.inductionOn s ?_
    intro u
    rfl
  right_inv := by
    intro s
    refine Quotient.inductionOn s ?_
    intro u
    rfl

/-- Consequently the tests of the prefix realization separate Nerode states:
    the Nerode quotient is the identifiable state object of `ρ`. -/
theorem prefixSystem_collapse_extensional (ρ : Recognizer Sym Q O) :
    ρ.prefixSystem.extensionalCollapse.Extensional :=
  ObservationSystem.extensionalCollapse_is_extensional ρ.prefixSystem

/-! ### The behavioral monoid acts on the Nerode quotient -/

/-- Right identity is a right congruence. -/
theorem rightEquiv_append_right {ρ : Recognizer Sym Q O} {u v : List Sym}
    (z : List Sym) (h : ρ.RightEquiv u v) : ρ.RightEquiv (u ++ z) (v ++ z) := by
  intro y q
  have := h (z ++ y) q
  simpa [List.append_assoc] using this

/-- Two-sided identity of the appended word preserves right identity. -/
theorem rightEquiv_append_of_contextEquiv {ρ : Recognizer Sym Q O} (w : List Sym)
    {u v : List Sym} (h : ρ.ContextEquiv u v) : ρ.RightEquiv (w ++ u) (w ++ v) := by
  intro z q
  exact h w z q

/-- The transition action: a behavioral class acts on a Nerode state by right
    concatenation, `[w] · [u] = [w ++ u]`. -/
def Nerode.act (ρ : Recognizer Sym Q O) : ρ.Nerode → ρ.Behavior → ρ.Nerode :=
  Quotient.lift₂ (fun w u => Quotient.mk ρ.rightSetoid (w ++ u))
    fun _ _ _ _ hw hu => Quotient.sound
      (rightEquiv_trans (rightEquiv_append_right _ hw) (rightEquiv_append_of_contextEquiv _ hu))

@[simp]
theorem Nerode.act_mk (ρ : Recognizer Sym Q O) (w u : List Sym) :
    Nerode.act ρ (Quotient.mk ρ.rightSetoid w) (Quotient.mk ρ.contextSetoid u) =
      Quotient.mk ρ.rightSetoid (w ++ u) :=
  rfl

/-- Acting by a product is acting twice: `B` acts as the transition monoid. -/
theorem Nerode.act_mul (ρ : Recognizer Sym Q O) (s : ρ.Nerode) (a b : ρ.Behavior) :
    Nerode.act ρ s (Behavior.mul ρ a b) = Nerode.act ρ (Nerode.act ρ s a) b := by
  refine Quotient.inductionOn₃ s a b ?_
  intro w u v
  simp [List.append_assoc]

/-- The empty class acts trivially. -/
theorem Nerode.act_one (ρ : Recognizer Sym Q O) (s : ρ.Nerode) :
    Nerode.act ρ s (Behavior.one ρ) = s := by
  refine Quotient.inductionOn s ?_
  intro w
  simp [Behavior.one]

/-- The initial state is the class of the empty trace, and every state is
    reached from it: the Nerode quotient is generated by the action. -/
theorem Nerode.reach (ρ : Recognizer Sym Q O) (s : ρ.Nerode) :
    ∃ a : ρ.Behavior, Nerode.act ρ (Quotient.mk ρ.rightSetoid []) a = s := by
  refine Quotient.inductionOn s ?_
  intro w
  exact ⟨Quotient.mk ρ.contextSetoid w, rfl⟩

end Recognizer

end RecognitionPaths
