namespace RecognitionPaths

universe u

/-- `R.Refines S` means that every `R`-identification is also an
    `S`-identification. -/
def Refines {X : Type u} (R S : Setoid X) : Prop :=
  ∀ ⦃x y : X⦄, R.Rel x y → S.Rel x y

/-- The canonical map between quotients induced by refinement. -/
def quotientMap {X : Type u} (R S : Setoid X) (h : Refines R S) :
    Quotient R → Quotient S :=
  Quotient.lift (fun x => Quotient.mk S x) fun _ _ hxy =>
    Quotient.sound (h hxy)

@[simp]
theorem quotientMap_mk {X : Type u} (R S : Setoid X) (h : Refines R S)
    (x : X) :
    quotientMap R S h (Quotient.mk R x) = Quotient.mk S x :=
  rfl

/-- Any map that sends representatives to their canonical `S`-classes is the
    canonical quotient map. -/
theorem quotientMap_unique {X : Type u} (R S : Setoid X) (h : Refines R S)
    (f : Quotient R → Quotient S)
    (hf : ∀ x, f (Quotient.mk R x) = Quotient.mk S x) :
    f = quotientMap R S h := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simpa using hf x

/-- A representative-preserving map between the two quotients forces the
    corresponding refinement of observational identities. -/
theorem refinement_of_factor {X : Type u} (R S : Setoid X)
    (f : Quotient R → Quotient S)
    (hf : ∀ x, f (Quotient.mk R x) = Quotient.mk S x) :
    Refines R S := by
  intro x y hxy
  apply Quotient.exact
  calc
    Quotient.mk S x = f (Quotient.mk R x) := (hf x).symm
    _ = f (Quotient.mk R y) := congrArg f (Quotient.sound hxy)
    _ = Quotient.mk S y := hf y

/-- Recognition Factorization Theorem: refinement is equivalent to the unique
    existence of the canonical representative-preserving quotient map. -/
theorem recognition_factorization_iff {X : Type u} (R S : Setoid X) :
    Refines R S ↔
      ∃! f : Quotient R → Quotient S,
        ∀ x, f (Quotient.mk R x) = Quotient.mk S x := by
  constructor
  · intro h
    refine ⟨quotientMap R S h, ?_, ?_⟩
    · exact quotientMap_mk R S h
    · intro f hf
      exact quotientMap_unique R S h f hf
  · rintro ⟨f, hf, _⟩
    exact refinement_of_factor R S f hf

end RecognitionPaths
