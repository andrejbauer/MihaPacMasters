open import Parameters

module Terms (P : Params) where

open import Types P

open Params P

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

    sub-value : {X X′ : VType}
        → Γ ⊢V: X
        → X ⊑ᵥ X′
        ------------------
        → Γ ⊢V: X′

    value-unit :
        --------------------
        Γ ⊢V: gnd unit

    value-pair : {X Y : VType}
        → Γ ⊢V: X
        → Γ ⊢V: Y
        -------------------
        → Γ ⊢V: X × Y

    
    user-fun : {X Y : VType} {U : Sig}
         → Γ ∷ X ⊢M: Y ! U
         ---------------------
         → Γ ⊢V: X ⟶ᵤ Y ! U
    
    kern-fun : {X Y : VType} {U : Sig} {C : KState}
         → (Γ ∷ X) ⊢K: Y ↯ U , C
         ------------------------------
         → Γ ⊢V: X ⟶ₖ Y ↯ U , C
    -- TyValue-Const

    -- unit :

    -- ...

  data _⊢M:_ where
    
    sub-user : {X X′ : VType} {U U′ : Sig}
         → Γ ⊢M: X ! U
         → X ! U ⊑ᵤ X′ ! U′
         -----------------------
         → Γ ⊢M: X′ ! U′


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

    try : {X Y : VType} { U : Sig }
    -- Without exceptions this one seems pointless
      → Γ ⊢M: X ! U
      → Γ ∷ X ⊢M: Y ! U
      → Γ ⊢M: Y ! U
      ----------
      → Γ ⊢M: Y ! U

    matchpair : {X Y Z : VType} {U : Sig}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢M: Z ! U
      ----------------------------
      → Γ ⊢M: Z ! U

    matchempty : {Z : VType} {U : Sig}
      → Γ ⊢V: gnd empty
      ---------------------
      → Γ ⊢M: Z ! U

   -- op : {U : Sig}
   --   → {!!}

    run : {U U′ : Sig} {C : KState} {X Y : VType}
      → Γ ⊢V: U ⇒ U′ , C
      → Γ ⊢V: gnd C -- Not entirely sure about this
      → Γ ⊢M: X ! U
      → Γ ∷ X ∷ gnd C ⊢M: Y ! U′
      → Γ ∷ gnd C ⊢M: Y ! U′
      → Γ ⊢M: Y ! U′
      -----------------
      → Γ ⊢M: Y ! U′


    user-kernel :{X Y : VType} {U : Sig} {C : KState}
      → Γ ⊢K: X ↯ U , C
      → Γ ⊢V: gnd C
      → Γ ∷ X ∷ gnd C ⊢M: Y ! U 
      → Γ ∷ gnd C ⊢M: Y ! U
      → Γ ⊢M: Y ! U
      --------------
      → Γ ⊢M: Y ! U 

    comp1 : {X Y : VType} {U : Sig}
     → Γ ∷ X ⊢M: Y ! U
     → Γ ⊢V: X
     ------------------------
     → Γ ⊢M: Y ! U

    comp2 : {!!}

  data _⊢K:_ where

    sub-kernel : {X X′ : VType} {U U′ : Sig} { C C′ : KState}
         → Γ ⊢K: X ↯ U , C
         → X ↯ U , C ⊑ₖ X′ ↯ U′ , C′
         ------------------------------------
         → Γ ⊢K: X′ ↯ U′ , C′



    return : {X : VType} {U : Sig} {C : KState}
      → Γ ⊢V: X
      --------------------------
      → Γ ⊢K: X ↯ U , C

    apply : {X Y : VType} {U : Sig} {C : KState}
      → Γ ⊢V: X ⟶ₖ Y ↯ U , C
      → Γ ⊢V: X
      ---------------------------------
      → Γ ⊢K: Y ↯ U , C

    try : {X Y : VType} {U : Sig} {C : KState}
      → Γ ⊢K: X ↯ U , C
      → Γ ⊢K: Y ↯ U , C
      → Γ ⊢K: Y ↯ U , C
      ---------------------------
      → Γ ⊢K: Y ↯ U , C

    matchpair : {X Y Z : VType} { U : Sig } {C : KState}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢K: Z ↯ U , C
      ---------------------
      → Γ ⊢K: Z ↯ U , C

    matchempty : {Z : VType} {U : Sig} {C : KState}
      → Γ ⊢V: gnd empty
      --------------------------
      → Γ ⊢K: Z ↯ U , C

    getenv : {C : KState} {X : VType} {U : Sig}
      → Γ ∷ gnd C ⊢K: X ↯ U , C
      ---------------------------
      → Γ ⊢K: X ↯ U , C

    setenv : {C : KState} {X : VType} {U : Sig}
      → Γ ⊢V: gnd C
      → Γ ⊢K: X ↯ U , C
      -------------------------
      → Γ ⊢K: X ↯ U , C

    kernel-user : {U : Sig} {C : KState} {X Y : VType}
      → Γ ⊢M: X ! U
      → Γ ∷ X ⊢K: Y ↯ U , C
      → Γ ⊢K: Y ↯ U , C
      --------------------------
      → Γ ⊢K: Y ↯ U , C
      

infix 1 _⊢M:_ _⊢K:_ _⊢V:_ 
