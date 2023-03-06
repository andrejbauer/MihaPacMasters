open import Data.Bool
open import Relation.Binary.PropositionalEquality

module Parameters where

record GTypes : Set₁ where
  field
    BaseType : Set

  data GType : Set where
    base : BaseType → GType
    unit : GType
    _×_  : GType → GType → GType -- Written as "\x"

-- Operations
record Ops (G : GTypes) : Set₁ where
  open GTypes G
  field
    Op : Set
    param  : Op → GType
    result : Op → GType

  -- Operation signatures
  Sig = Op → Bool

  _∈ₒ_ : Op → Sig → Set
  op ∈ₒ Σ = Σ op ≡ true
