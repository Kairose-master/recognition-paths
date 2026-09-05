namespace RecognitionPaths

universe u v w

/-- A black-box realization exposes states only through a family of tests. -/
structure ObservationSystem (Test : Type v) (Output : Type w) where
  State : Type u
  observe : State → Test → Output

namespace ObservationSystem

/-- The complete observable profile of a state under the chosen tests. -/
def profile {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output) : A.State → Test → Output :=
  A.observe

/-- A realization is extensional when its tests separate all of its states. -/
def Extensional {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output) : Prop :=
  Function.Injective A.profile

/-- A map of realizations that preserves every specified observation. -/
def Preserves {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output)
    (B : ObservationSystem.{u, v, w} Test Output)
    (f : A.State → B.State) : Prop :=
  ∀ s t, B.observe (f s) t = A.observe s t

/-- Add one hidden Boolean coordinate that no test can inspect. -/
def silentExtension {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output) :
    ObservationSystem.{u, v, w} Test Output where
  State := A.State × Bool
  observe sb := A.observe sb.1

/-- The original realization embeds into its silent extension without changing
    any observation. -/
theorem silentEmbedding_preserves {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output) :
    A.Preserves A.silentExtension (fun s => (s, false)) := by
  intro s t
  rfl

/-- Forgetting the silent coordinate also preserves every observation. -/
theorem silentProjection_preserves {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output) :
    A.silentExtension.Preserves A Prod.fst := by
  intro s t
  rfl

/-- No family of tests in `A` can distinguish the two lifts of any state. -/
theorem silent_lifts_have_identical_profiles {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output) (s : A.State) :
    A.silentExtension.profile (s, false) =
      A.silentExtension.profile (s, true) := by
  rfl

/-- Observations alone do not force a realization to be extensional: every
    inhabited realization has an observationally silent, non-extensional
    extension.  This is the elementary non-identifiability obstruction. -/
theorem silentExtension_not_extensional {Test : Type v} {Output : Type w}
    (A : ObservationSystem.{u, v, w} Test Output) [Nonempty A.State] :
    ¬ A.silentExtension.Extensional := by
  intro h
  let s : A.State := Classical.choice (inferInstance : Nonempty A.State)
  have hp : A.silentExtension.profile (s, false) =
      A.silentExtension.profile (s, true) :=
    silent_lifts_have_identical_profiles A s
  have hs : (s, false) = (s, true) := h hp
  have hb : false = true := congrArg Prod.snd hs
  cases hb

end ObservationSystem

end RecognitionPaths
