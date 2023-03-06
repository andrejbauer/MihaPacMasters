open import Parameters

module Terms (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open import Types G O
open import Contexts G O

-- replaced ⦂ with ː because my computer's font does not show the former.
-- ː is \:3
-- Replaced ː with :, because I don't see the point
-- Well-typed value and computation terms
interleaved mutual

  data _⊢V:_ (Γ : Ctx) : VType → Set  -- \vdash \:2
  data _⊢M:_ (Γ : Ctx) : UType → Set  -- \:2
  data _⊢K:_ (Γ : Ctx) : KType → Set  -- \:2
  
  data _⊢V:_ where

    var : {X : VType}
        → X ∈ Γ          -- constructively, exists a variable with type X in Γ
        -------------
        → Γ ⊢V: X

    value-coerce : {X X' : VType}
        → Γ ⊢V: X
        → X ⊑ᵥ X'
        ------------------
        → Γ ⊢V: X'

    ⟨⟩ :
        --------------------
        Γ ⊢V: gnd unit

    value-pair : {X Y : VType}
        → Γ ⊢V: X
        → Γ ⊢V: Y
        -------------------
        → Γ ⊢V: X × Y

    user-fun : {X : VType} {U : UType}
         → Γ ∷ X ⊢M: U
         ---------------------
         → Γ ⊢V: X ⟶ᵤ U
    
    kern-fun : {X Y : VType} {U : Sig} {C : KState}
         → (Γ ∷ X) ⊢K: Y ↯ U , C
         ------------------------------
         → Γ ⊢V: X ⟶ₖ Y ↯ U , C

    runner : {Σ Σ' : Sig} {C : KState} {op : Op}
         → ((op ∈ₒ Σ) → Γ ∷ gnd (param op) ⊢K: gnd (result op) ↯ Σ' , C)
         ---------------------------------------------------------------
         → Γ ⊢V: Σ ⇒ Σ' , C

  data _⊢M:_ where
    
    sub-user : {X X' : VType} {U U' : Sig}
         → Γ ⊢M: X ! U
         → X ! U ⊑ᵤ X' ! U'
         -----------------------
         → Γ ⊢M: X' ! U'

    return : {X : VType} {U : Sig}
    -- TyUser-Return
       → Γ ⊢V: X
       ----------
       → Γ ⊢M: X ! U

    apply : {X Y : VType} {U : Sig}
      → Γ ⊢V: X ⟶ᵤ Y ! U
      → Γ ⊢V: X
      -------------------------
      → Γ ⊢M: Y ! U

    -- _(*)_

    `let_`in : {X Y : VType} { U : Sig }
    -- Without exceptions this one seems pointless
    -- let x = M in N
      → Γ ⊢M: X ! U
      → Γ ∷ X ⊢M: Y ! U
      ----------
      → Γ ⊢M: Y ! U

    matchpair : {X Y Z : VType} {U : Sig}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢M: Z ! U
      ----------------------------
      → Γ ⊢M: Z ! U

   -- op : {U : Sig}
   --   → {!!}

    `using_at_run_finally : {U U' : Sig} {C : KState} {X Y : VType}
      → Γ ⊢V: U ⇒ U' , C
      → Γ ⊢V: gnd C
      → Γ ⊢M: X ! U
      → Γ ∷ X ∷ gnd C ⊢M: Y ! U'
      -----------------
      → Γ ⊢M: Y ! U'

    -- `using R at W run M finally N
    -- vs
    -- run R W M N


    kernel_at_finally :{X Y : VType} {U : Sig} {C : KState}
      → Γ ⊢K: X ↯ U , C
      → Γ ⊢V: gnd C
      → Γ ∷ X ∷ gnd C ⊢M: Y ! U 
      --------------
      → Γ ⊢M: Y ! U 

  data _⊢K:_ where

    sub-kernel : {X X' : VType} {U U' : Sig} { C C' : KState}
         → Γ ⊢K: X ↯ U , C
         → X ↯ U , C ⊑ₖ X' ↯ U' , C'
         ------------------------------------
         → Γ ⊢K: X' ↯ U' , C'



    return : {X : VType} {U : Sig} {C : KState}
      → Γ ⊢V: X
      --------------------------
      → Γ ⊢K: X ↯ U , C

    apply : {X Y : VType} {U : Sig} {C : KState}
      → Γ ⊢V: X ⟶ₖ Y ↯ U , C
      → Γ ⊢V: X
      ---------------------------------
      → Γ ⊢K: Y ↯ U , C

    `let_`in : {X Y : VType} {U : Sig} {C : KState}
      → Γ ⊢K: X ↯ U , C
      → Γ ∷ X ⊢K: Y ↯ U , C
      ---------------------------
      → Γ ⊢K: Y ↯ U , C

    matchpair : {X Y Z : VType} { U : Sig } {C : KState}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢K: Z ↯ U , C
      ---------------------
      → Γ ⊢K: Z ↯ U , C

    -- TODO: ops

    getenv : {C : KState} {X : VType} {U : Sig}
      → Γ ∷ gnd C ⊢K: X ↯ U , C
      ---------------------------
      → Γ ⊢K: X ↯ U , C

    setenv : {C : KState} {X : VType} {U : Sig}
      → Γ ⊢V: gnd C
      → Γ ⊢K: X ↯ U , C
      -------------------------
      → Γ ⊢K: X ↯ U , C

    user_finally : {U : Sig} {C : KState} {X Y : VType}
      → Γ ⊢M: X ! U
      → Γ ∷ X ⊢K: Y ↯ U , C
      --------------------------
      → Γ ⊢K: Y ↯ U , C
      

infix 1 _⊢M:_ _⊢K:_ _⊢V:_ 
