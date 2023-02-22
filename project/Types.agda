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
    _⟶_  : VType → VType → VType -- "\r--"
    _⇒_,_ : Sig → Sig → KState → VType -- "\r="
 
  --- User type
  data UType where
    _!_ : VType → Sig → UType
 
  --- Kernel Type
  data KType where
    _↯_,_ : VType → Sig → KState → KType   --"\dz = ↯"
 
-- Subtyping relations
_⊆ₛ_ : Sig → Sig → Set
Σ ⊆ₛ Σ' = (op : Op) → Σ op ≡ true → Σ' op ≡ true

interleaved mutual
  data _⊑ᵥ_ : VType → VType → Set
  data _⊑ᵤ_ : UType → UType → Set
  data _⊑ₖ_ : KType → KType → Set

  data _⊑ᵥ_ where -- "\squb="

    --  I wrote ⊑ᵥ as "\squb\_v and then choosing the 4th v
    ⊑ᵥ-ground : {A : GType}
              -------------
              → gnd A ⊑ᵥ gnd A
  
    ⊑ᵥ-product : {X Y Z W : VType}
               → X ⊑ᵥ Z
               → Y ⊑ᵥ W
               --------------------
                 → (X × Y) ⊑ᵥ (Z × W)

    ⊑ᵥ-runner : {U U′ V V′ : Sig} {C : KState} -- I assume ≡ means equality
               → U′ ⊆ₛ U
               → V ⊆ₛ V′
               --------------
               → U ⇒ V , C ⊑ᵥ U′ ⇒ V′ , C
              

  data _⊑ᵤ_ where

    ⊑ᵤ-fun : {X X′ Y Y′ : VType} {U U′ : Sig}
                → X′ ⊑ᵥ X
                → Y ! U ⊑ᵤ Y′ ! U′
                -----------------------
                → X ⟶ Y ! U ⊑ᵤ X′ ⟶ Y′ ! U′

    ⊑ᵤ-ground : {X X′ : VType} {U U′ : Sig}
                → X ⊑ᵥ X′
                → U ⊆ₛ U′
                → X ! U ⊑ᵤ X′ ! U′

  data _⊑ₖ_ where

    ⊑ₖ-fun : {X X′ Y Y′ : VType} {U U′ : Sig} {C C′ : KState}
                → X′ ⊑ᵥ X
                → Y ↯ U , C ⊑ₖ Y′ ↯ U′ , C′
                -----------------------------------
                → X ⟶ Y ↯ U , C ⊑ₖ X′ ⟶ Y′ ↯ U′ , C′

    ⊑ₖ-ground : {X X′ : VType} {U U′ : Sig} {C : KState}
                → X ⊑ᵥ X′
                → U ⊆ₛ U′
                ---------------------------
                → X ↯ U , C ⊑ₖ X′ ↯ U′ , C
  -- That might be it
 
-- Contexts (using De Bruijn indices)
data Ctx : Set where
  []  : Ctx
  _∷_ : Ctx → VType → Ctx

-- Variables in context
data _∈_ : VType → Ctx → Set where                         -- x : X ∈ Γ
  here  : {X : VType} {Γ : Ctx} → X ∈ (Γ ∷ X)
  there : {X Y : VType} {Γ : Ctx} → X ∈ Γ → X ∈ (Γ ∷ Y)
 

infix 10 _⊑ᵥ_ _⊑ᵤ_ _⊑ₖ_
infix 20 _⟶_ _⇒_,_
infix 15 _!_ _↯_,_
infix 40 _×_


-- ...
