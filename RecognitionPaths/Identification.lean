import RecognitionPaths.Nerode

/-!
# When does a finite test family identify the recognition congruence?

An experiment observes a recognizer only on a chosen family of tests `T`.
The relation it can measure is `≡_{ρ,T}` (agreement on `T`), which is always
coarser than the full right-context identity `≡_ρ`.  This file proves the
exact set-level criterion for equality:

* **Identification.**  If `T` contains the direct queries `([], q)` and the
  relation `≡_{ρ,T}` is closed under appending one symbol, then
  `≡_{ρ,T} = ≡_ρ`.  Closure is Angluin's *consistency* condition on an
  observation table, stated globally.
* **Refinement witness.**  If `T` is not closed, there is a concrete pair
  identified by `T` and a concrete test `(a :: z, q)`, one symbol longer than
  a test in `T`, that separates it.  This is the column-refinement step of
  Angluin's algorithm, so the criterion is constructive: a failure names the
  next column to add.
* **Stabilisation.**  For length-bounded families `T_k`, as soon as `T_k` and
  `T_{k+1}` induce the same relation, `T_k` identifies `≡_ρ`.

The two-sided versions for `≈_ρ` follow the same pattern.

The classical counting bound (`n` Nerode classes force stabilisation by
`k = n - 1`) is not formalised here; it needs a pigeonhole argument that this
Mathlib-free development does not carry.  It is recorded as OPEN in the docs.
No linear-algebraic (Hankel rank) statement is made.
-/

namespace RecognitionPaths

universe u v w

namespace Recognizer

variable {Sym : Type u} {Q : Type v} {O : Type w}

/-! ### Right-context identity on a test family -/

/-- Right-context identity relative to a family of tests `(z, q)`. -/
def RightEquivOn (ρ : Recognizer Sym Q O) (T : List Sym → Q → Prop)
    (u v : List Sym) : Prop :=
  ∀ (z : List Sym) (q : Q), T z q → ρ.observe (u ++ z) q = ρ.observe (v ++ z) q

/-- Full identity implies identity on every test family. -/
theorem rightEquivOn_of_rightEquiv {ρ : Recognizer Sym Q O}
    (T : List Sym → Q → Prop) {u v : List Sym} (h : ρ.RightEquiv u v) :
    ρ.RightEquivOn T u v :=
  fun z q _ => h z q

theorem rightEquivOn_refl (ρ : Recognizer Sym Q O) (T : List Sym → Q → Prop)
    (u : List Sym) : ρ.RightEquivOn T u u :=
  fun _ _ _ => rfl

theorem rightEquivOn_symm {ρ : Recognizer Sym Q O} {T : List Sym → Q → Prop}
    {u v : List Sym} (h : ρ.RightEquivOn T u v) : ρ.RightEquivOn T v u :=
  fun z q hz => (h z q hz).symm

theorem rightEquivOn_trans {ρ : Recognizer Sym Q O} {T : List Sym → Q → Prop}
    {u v t : List Sym} (h₁ : ρ.RightEquivOn T u v) (h₂ : ρ.RightEquivOn T v t) :
    ρ.RightEquivOn T u t :=
  fun z q hz => (h₁ z q hz).trans (h₂ z q hz)

/-- A test family contains the direct queries when it can ask every query with
    the empty continuation. -/
def Direct (T : List Sym → Q → Prop) : Prop :=
  ∀ q : Q, T [] q

/-- A test family is *closed* for `ρ` when the identity it induces survives
    appending one symbol.  This is Angluin's consistency condition. -/
def Closed (ρ : Recognizer Sym Q O) (T : List Sym → Q → Prop) : Prop :=
  ∀ u v, ρ.RightEquivOn T u v → ∀ a : Sym, ρ.RightEquivOn T (u ++ [a]) (v ++ [a])

/-- Under closure, the induced identity survives appending any word. -/
theorem rightEquivOn_append_of_closed {ρ : Recognizer Sym Q O}
    {T : List Sym → Q → Prop} (hT : ρ.Closed T) :
    ∀ (z u v : List Sym), ρ.RightEquivOn T u v → ρ.RightEquivOn T (u ++ z) (v ++ z) := by
  intro z
  induction z with
  | nil =>
    intro u v h
    simpa using h
  | cons a z ih =>
    intro u v h
    have h' := hT u v h a
    have := ih (u ++ [a]) (v ++ [a]) h'
    simpa [List.append_assoc] using this

/-- **Identification theorem.**  A closed test family containing the direct
    queries identifies right-context identity exactly. -/
theorem rightEquiv_of_closed {ρ : Recognizer Sym Q O} {T : List Sym → Q → Prop}
    (hD : Direct T) (hT : ρ.Closed T) {u v : List Sym}
    (h : ρ.RightEquivOn T u v) : ρ.RightEquiv u v := by
  intro z q
  have := rightEquivOn_append_of_closed hT z u v h [] q (hD q)
  simpa using this

theorem rightEquiv_iff_rightEquivOn {ρ : Recognizer Sym Q O} {T : List Sym → Q → Prop}
    (hD : Direct T) (hT : ρ.Closed T) (u v : List Sym) :
    ρ.RightEquiv u v ↔ ρ.RightEquivOn T u v :=
  ⟨rightEquivOn_of_rightEquiv T, rightEquiv_of_closed hD hT⟩

/-- Closure is also necessary: if `T` identifies `≡_ρ`, then `T` is closed. -/
theorem closed_of_identifies {ρ : Recognizer Sym Q O} {T : List Sym → Q → Prop}
    (hI : ∀ u v, ρ.RightEquivOn T u v → ρ.RightEquiv u v) : ρ.Closed T := by
  intro u v h a
  exact rightEquivOn_of_rightEquiv T (rightEquiv_append_right [a] (hI u v h))

/-- **Refinement witness.**  A test family that is not closed identifies a pair
    that some one-symbol-longer test separates.  That test is the column to add. -/
theorem refine_witness {ρ : Recognizer Sym Q O} {T : List Sym → Q → Prop}
    (hT : ¬ ρ.Closed T) :
    ∃ (u v : List Sym) (a : Sym) (z : List Sym) (q : Q),
      ρ.RightEquivOn T u v ∧ T z q ∧
        ρ.observe (u ++ a :: z) q ≠ ρ.observe (v ++ a :: z) q := by
  unfold Closed at hT
  rcases Classical.not_forall.mp hT with ⟨u, hu⟩
  rcases Classical.not_forall.mp hu with ⟨v, hv⟩
  rcases Classical.not_imp.mp hv with ⟨huv, hna⟩
  rcases Classical.not_forall.mp hna with ⟨a, ha⟩
  unfold RightEquivOn at ha
  rcases Classical.not_forall.mp ha with ⟨z, hz⟩
  rcases Classical.not_forall.mp hz with ⟨q, hq⟩
  rcases Classical.not_imp.mp hq with ⟨hTz, hne⟩
  refine ⟨u, v, a, z, q, huv, hTz, ?_⟩
  simpa [List.append_assoc] using hne

/-! ### Length-bounded test families -/

/-- All tests whose continuation has length at most `k`. -/
def upTo (k : Nat) : List Sym → Q → Prop :=
  fun z _ => z.length ≤ k

theorem upTo_direct (k : Nat) : Direct (upTo (Sym := Sym) (Q := Q) k) :=
  fun _ => Nat.zero_le k

/-- Identity on continuations of length at most `k`. -/
abbrev BoundedEquiv (ρ : Recognizer Sym Q O) (k : Nat) : List Sym → List Sym → Prop :=
  ρ.RightEquivOn (upTo k)

/-- Longer test families are finer. -/
theorem boundedEquiv_of_succ {ρ : Recognizer Sym Q O} {k : Nat} {u v : List Sym}
    (h : ρ.BoundedEquiv (k + 1) u v) : ρ.BoundedEquiv k u v :=
  fun z q hz => h z q (Nat.le_succ_of_le hz)

/-- One more level of continuation is exactly one more symbol of prefix. -/
theorem boundedEquiv_succ_iff (ρ : Recognizer Sym Q O) (k : Nat) (u v : List Sym) :
    ρ.BoundedEquiv (k + 1) u v ↔
      ρ.BoundedEquiv 0 u v ∧ ∀ a : Sym, ρ.BoundedEquiv k (u ++ [a]) (v ++ [a]) := by
  constructor
  · intro h
    refine ⟨fun z q hz => h z q (Nat.le_trans hz (Nat.zero_le _)), ?_⟩
    intro a z q hz
    have := h (a :: z) q (by simpa [upTo] using Nat.succ_le_succ hz)
    simpa [List.append_assoc] using this
  · rintro ⟨h0, hs⟩ z q hz
    cases z with
    | nil => exact h0 [] q (Nat.le_refl 0)
    | cons a z =>
      have := hs a z q (Nat.le_of_succ_le_succ hz)
      simpa [List.append_assoc] using this

/-- **Stabilisation.**  If level `k` already induces the identity of level
    `k + 1`, then level `k` is closed. -/
theorem closed_of_stable {ρ : Recognizer Sym Q O} {k : Nat}
    (hs : ∀ u v, ρ.BoundedEquiv k u v → ρ.BoundedEquiv (k + 1) u v) :
    ρ.Closed (upTo k) := by
  intro u v h a
  exact ((ρ.boundedEquiv_succ_iff k u v).mp (hs u v h)).2 a

/-- Hence a stable level identifies `≡_ρ`: the finite family `T_k` suffices. -/
theorem rightEquiv_of_stable {ρ : Recognizer Sym Q O} {k : Nat}
    (hs : ∀ u v, ρ.BoundedEquiv k u v → ρ.BoundedEquiv (k + 1) u v)
    {u v : List Sym} (h : ρ.BoundedEquiv k u v) : ρ.RightEquiv u v :=
  rightEquiv_of_closed (upTo_direct k) (closed_of_stable hs) h

/-! ### The two-sided version for the recognition congruence -/

/-- A two-sided test family contains the direct queries. -/
def Direct₂ (T : List Sym → List Sym → Q → Prop) : Prop :=
  ∀ q : Q, T [] [] q

/-- Two-sided closure: the induced identity survives one symbol on either
    side. -/
def Closed₂ (ρ : Recognizer Sym Q O) (T : List Sym → List Sym → Q → Prop) : Prop :=
  ∀ u v, ρ.ContextEquivOn T u v →
    ∀ a : Sym, ρ.ContextEquivOn T (u ++ [a]) (v ++ [a]) ∧
      ρ.ContextEquivOn T ([a] ++ u) ([a] ++ v)

theorem contextEquivOn_append_right_of_closed {ρ : Recognizer Sym Q O}
    {T : List Sym → List Sym → Q → Prop} (hT : ρ.Closed₂ T) :
    ∀ (z u v : List Sym), ρ.ContextEquivOn T u v → ρ.ContextEquivOn T (u ++ z) (v ++ z) := by
  intro z
  induction z with
  | nil =>
    intro u v h
    simpa using h
  | cons a z ih =>
    intro u v h
    have := ih (u ++ [a]) (v ++ [a]) (hT u v h a).1
    simpa [List.append_assoc] using this

theorem contextEquivOn_append_left_of_closed {ρ : Recognizer Sym Q O}
    {T : List Sym → List Sym → Q → Prop} (hT : ρ.Closed₂ T) :
    ∀ (x u v : List Sym), ρ.ContextEquivOn T u v → ρ.ContextEquivOn T (x ++ u) (x ++ v) := by
  intro x
  induction x with
  | nil =>
    intro u v h
    simpa using h
  | cons a x ih =>
    intro u v h
    have := (hT (x ++ u) (x ++ v) (ih u v h) a).2
    simpa using this

/-- **Two-sided identification theorem.**  A two-sided closed test family
    containing the direct queries identifies the recognition congruence. -/
theorem contextEquiv_of_closed₂ {ρ : Recognizer Sym Q O}
    {T : List Sym → List Sym → Q → Prop} (hD : Direct₂ T) (hT : ρ.Closed₂ T)
    {u v : List Sym} (h : ρ.ContextEquivOn T u v) : ρ.ContextEquiv u v := by
  intro x z q
  have h₁ := contextEquivOn_append_right_of_closed hT z u v h
  have h₂ := contextEquivOn_append_left_of_closed hT x (u ++ z) (v ++ z) h₁
  have := h₂ [] [] q (hD q)
  simpa [List.append_assoc] using this

theorem contextEquiv_iff_contextEquivOn {ρ : Recognizer Sym Q O}
    {T : List Sym → List Sym → Q → Prop} (hD : Direct₂ T) (hT : ρ.Closed₂ T)
    (u v : List Sym) : ρ.ContextEquiv u v ↔ ρ.ContextEquivOn T u v :=
  ⟨contextEquivOn_of_contextEquiv T, contextEquiv_of_closed₂ hD hT⟩

/-- Two-sided closure is necessary as well. -/
theorem closed₂_of_identifies {ρ : Recognizer Sym Q O}
    {T : List Sym → List Sym → Q → Prop}
    (hI : ∀ u v, ρ.ContextEquivOn T u v → ρ.ContextEquiv u v) : ρ.Closed₂ T := by
  intro u v h a
  exact ⟨contextEquivOn_of_contextEquiv T (contextEquiv_append_right [a] (hI u v h)),
    contextEquivOn_of_contextEquiv T (contextEquiv_append_left [a] (hI u v h))⟩

end Recognizer

end RecognitionPaths
