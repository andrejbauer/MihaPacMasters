open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Parameters

module Types (P : Params) where

open Params P

-- Ground types
data GType : Set where
  base : BaseType → GType
  unit : GType
  empty : GType
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
    _⟶ₖ_ : VType → KType → VType
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

_≡ₖ_ : KState → KState → Set
C ≡ₖ C′ = C ≡ C′

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

    
    ⊑ᵥ-Ufun : {X X′ Y Y′ : VType} {U U′ : Sig}
                → X′ ⊑ᵥ X
                → Y ! U ⊑ᵤ Y′ ! U′
                -----------------------
                → X ⟶ᵤ Y ! U ⊑ᵥ X′ ⟶ᵤ Y′ ! U′

    ⊑ᵥ-Kfun : {X X′ Y Y′ : VType} {U U′ : Sig} {C C′ : KState}
                → X′ ⊑ᵥ X
                → Y ↯ U , C ⊑ₖ Y′ ↯ U′ , C′
                -----------------------------------
                → X ⟶ₖ Y ↯ U , C ⊑ᵥ X′ ⟶ₖ Y′ ↯ U′ , C′ 

    ⊑ᵥ-runner : {U U′ V V′ : Sig} {C C′ : KState}
               → U′ ⊆ₛ U
               → V ⊆ₛ V′
               → C ≡ C′
               --------------
               → U ⇒ V , C ⊑ᵥ U′ ⇒ V′ , C′

  data _⊑ᵤ_ where


    ⊑ᵤ-ground : {X X′ : VType} {U U′ : Sig}
                → X ⊑ᵥ X′
                → U ⊆ₛ U′
                → X ! U ⊑ᵤ X′ ! U′

  data _⊑ₖ_ where



    ⊑ₖ-kernel : {X X′ : VType} {U U′ : Sig} {C C′ : KState}
                → X ⊑ᵥ X′
                → U ⊆ₛ U′
                → C ≡ C′
                ---------------------------
                → X ↯ U , C ⊑ₖ X′ ↯ U′ , C′

    

  -- That might be it
 
-- Contexts (using De Bruijn indices)
data Ctx : Set where
  []  : Ctx
  _∷_ : Ctx → VType → Ctx

-- Variables in context
data _∈_ : VType → Ctx → Set where                         -- x : X ∈ Γ
  here  : {X : VType} {Γ : Ctx} → X ∈ (Γ ∷ X)
  there : {X Y : VType} {Γ : Ctx} → X ∈ Γ → X ∈ (Γ ∷ Y)


infixl 20 _∷_
infix 12 _⟶ᵤ_ _⟶ₖ_ _⇒_,_
infix 10 _⊑ᵥ_ _⊑ᵤ_ _⊑ₖ_
infix 15 _!_ _↯_,_
infix 40 _×_


-- ...
