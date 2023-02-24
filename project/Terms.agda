open import Parameters

module Terms (P : Params) where

open import Types P

open Params P

-- replaced ⦂ with ː because my computer's font does not show the former.
-- ː is \:3
-- Well-typed value and computation terms
interleaved mutual

  data _⊢Vː_ (Γ : Ctx) : VType → Set  -- \vdash \:2
  data _⊢Mː_ (Γ : Ctx) : UType → Set  -- \:2
  data _⊢Kː_ (Γ : Ctx) : KType → Set  -- \:2
  
  data _⊢Vː_ where

    var : {X : VType}
        → X ∈ Γ          -- constructively, exists a variable with type X in Γ
        -------------
        → Γ ⊢Vː X

    sub-value : {X X′ : VType}
        → Γ ⊢Vː X
        → X ⊑ᵥ X′
        ------------------
        → Γ ⊢Vː X′

    -- TyValue-Const

    -- unit :

    -- ...

  data _⊢Mː_ where
    
    sub-user : {X X′ : VType} {U U′ : Sig}
         → Γ ⊢Mː X ! U
         → X ! U ⊑ᵤ X′ ! U′
         -----------------------
         → Γ ⊢Mː X′ ! U′

  data _⊢Kː_ where

    sub-kernel : {X X′ : VType} {U U′ : Sig} { C C′ : KState}
         → Γ ⊢Kː X ↯ U , C
         → X ↯ U , C ⊑ₖ X′ ↯ U′ , C′
         ------------------------------------
         → Γ ⊢Kː X′ ↯ U′ , C′


infix 1 _⊢Mː_ _⊢Kː_ _⊢Vː_ 
