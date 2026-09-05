namespace RecognitionPaths

universe u v

/-- A bijection presented by mutually inverse functions.  Lean core has no
    `Equiv`; this local copy keeps the project free of Mathlib. -/
structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

@[inherit_doc] infixl:25 " ≃ " => Equiv

namespace Equiv

/-- Every type is equivalent to itself. -/
def refl (α : Sort u) : α ≃ α where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalences can be reversed. -/
def symm {α : Sort u} {β : Sort v} (e : α ≃ β) : β ≃ α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

end Equiv

end RecognitionPaths
