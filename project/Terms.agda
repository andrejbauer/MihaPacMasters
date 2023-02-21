open import Parameters

module Terms (P : Params) where

open import Types P

open Params P

-- Well-typed value and computation terms
interleaved mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set  -- \vdash \:2
  data _⊢M⦂_ (Γ : Ctx) : UType → Set  -- \:2
  data _⊢K⦂_ (Γ : Ctx) : KType → Set  -- \:2
  
  data _⊢V⦂_ where

    var : {X : VType}
        → X ∈ Γ          -- constructively, exists a variable with type X in Γ
        -------------
        → Γ ⊢V⦂ X

    -- ...

  data _⊢M⦂_ where

  data _⊢K⦂_ where
