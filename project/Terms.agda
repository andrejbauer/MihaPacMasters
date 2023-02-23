open import Parameters

module Terms (P : Params) where

open import Types P

open Params P

-- replaced ⦂ with ː because my computer's font does not show the former.
-- ː is \: and picking the 3rd option
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

  data _⊢Kː_ where
