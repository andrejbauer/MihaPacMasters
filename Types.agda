open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Parameters

module Types (P : Params) where

open Params P

-- Ground types
data GType : Set where
  base : BaseType → GType
  unit : GType
  _×_  : GType → GType → GType -- Written as "\x"
 
-- Operation signatures
Sig = Op → Bool
 
-- Kernel state type
KState = GType
 
 
interleaved mutual
  data VType : Set
  data UType : Set
  data KType : Set
  
  -- Value type
  data VType where
    gnd   : GType → VType
    _×_   : VType → VType → VType -- Written as "\x"
    _⟶ᵤ_  : VType → UType → VType -- "\r--"
    _⟶ₖ_  : VType → KType → VType
    _⇒_,_ : Sig → Sig → KState → VType
 
  --- User type
  data UType where
    _!_ : VType → Sig → UType
 
  --- Kernel Type
  data KType where
    _↯_,_ : VType → Sig → KState → KType   --"\dz = ↯"
 
-- Subtyping relations
_⊆ₛ_ : Sig → Sig → Set
Σ ⊆ₛ Σ' = (op : Op) → Σ op ≡ true → Σ' op ≡ true

data _⊑ᵥ_ : VType → VType → Set where
 
  ⊑ᵥ-ground : {A : GType}
            -------------
            → gnd A ⊑ᵥ gnd A
  
  ⊑ᵥ-product : {X Y Z W : VType}
             → X ⊑ᵥ Z
             → Y ⊑ᵥ W
             --------------------
             → (X × Y) ⊑ᵥ (Z × W)
  -- ...
 
-- Contexts (using De Bruijn indices)
data Ctx : Set where
  []  : Ctx
  _∷_ : Ctx → VType → Ctx

-- Variables in context
data _∈_ : VType → Ctx → Set where                         -- x : X ∈ Γ
  here  : {X : VType} {Γ : Ctx} → X ∈ (Γ ∷ X)
  there : {X Y : VType} {Γ : Ctx} → X ∈ Γ → X ∈ (Γ ∷ Y)
 
 
infix 20 _⟶ᵤ_ _⟶ₖ_
infix 30 _!_

-- ...
