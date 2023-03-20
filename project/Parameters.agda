open import Data.Bool
open import Relation.Binary.PropositionalEquality

module Parameters where

-- Ground types
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

-- Assuming given some ground types and operations
-- TODO: temporary fix, due to importing of parameterised
--       modules retaining qualified names of constructors
postulate G : GTypes
postulate O : Ops G
