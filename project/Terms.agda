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

  data _⊢V:_ (Γ : Ctx) : VType → Set  
  data _⊢M:_ (Γ : Ctx) : UType → Set
  data _⊢K:_ (Γ : Ctx) : KType → Set
  
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
    
    kern-fun : {X : VType} {K : KType}
         → (Γ ∷ X) ⊢K: K
         ------------------------------
         → Γ ⊢V: X ⟶ₖ K

    runner : {Σ Σ' : Sig} {C : KState} {op : Op}
         → ((op ∈ₒ Σ) → Γ ∷ gnd (param op) ⊢K: gnd (result op) ↯ Σ' , C)
         ---------------------------------------------------------------
         → Γ ⊢V: Σ ⇒ Σ' , C

  data _⊢M:_ where
    
    sub-user : {U U' : UType}
         → Γ ⊢M: U
         → U ⊑ᵤ U'
         -----------------------
         → Γ ⊢M: U'

    return : {X : VType} {Σ : Sig}
    -- TyUser-Return
       → Γ ⊢V: X
       ----------
       → Γ ⊢M: X ! Σ

    apply : {X : VType} {U : UType}
      → Γ ⊢V: X ⟶ᵤ U
      → Γ ⊢V: X
      -------------------------
      → Γ ⊢M: U

    -- _(*)_

--    tyuser-op : {X Y : VType} {Σ : Sig} {op : Op}
--       → ((op ∈ₒ Σ) → Γ ⊢V: X)
--       → ((op ∈ₒ Σ) → Γ ∷ Y ⊢M: X ! Σ)
--       -------------------------
--       → Γ ⊢M: X ! Σ

    tyuser-op : {X Y : VType} {Σ : Sig} {op : Op}
       → Γ ⊢V: X
       → Γ ∷ Y ⊢M: X ! Σ
       -------------------------
       → Γ ⊢M: X ! Σ

    `let_`in : {X Y : VType} { Σ : Sig }
    -- let x = M in N
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ⊢M: Y ! Σ
      ----------
      → Γ ⊢M: Y ! Σ

    matchpair : {X Y : VType} {U : UType}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢M: U
      ----------------------------
      → Γ ⊢M: U

   -- op : {Σ : Sig}
   --   → {!!}

    `using_at_run_finally : {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → Γ ⊢V: Σ ⇒ Σ' , C
      → Γ ⊢V: gnd C
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ∷ gnd C ⊢M: Y ! Σ'
      -----------------
      → Γ ⊢M: Y ! Σ'

    -- `using R at W run M finally N
    -- vs
    -- run R W M N


    kernel_at_finally :{X Y : VType} {Σ : Sig} {C : KState}
      → Γ ⊢K: X ↯ Σ , C
      → Γ ⊢V: gnd C
      → Γ ∷ X ∷ gnd C ⊢M: Y ! Σ 
      --------------
      → Γ ⊢M: Y ! Σ 

  data _⊢K:_ where

    sub-kernel : {K K' : KType}
         → Γ ⊢K: K
         → K ⊑ₖ K'
         ------------------------------------
         → Γ ⊢K: K'



    return : {X : VType} {Σ : Sig} {C : KState}
      → Γ ⊢V: X
      --------------------------
      → Γ ⊢K: X ↯ Σ , C

    apply : {X : VType} {K : KType}
      → Γ ⊢V: X ⟶ₖ K
      → Γ ⊢V: X
      ---------------------------------
      → Γ ⊢K: K

    `let_`in : {X Y : VType} {Σ : Sig} {C : KState}
      → Γ ⊢K: X ↯ Σ , C
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      ---------------------------
      → Γ ⊢K: Y ↯ Σ , C

    matchpair : {X Y : VType} {K : KType}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢K: K
      ---------------------
      → Γ ⊢K: K

    kernel-op : {X Y : VType} {Σ : Sig} {C : KState}
      → Γ ⊢V: X
      → Γ ∷ Y ⊢K: X ↯ Σ , C
      ------------------------------
      → Γ ⊢K: X ↯ Σ , C
    
    getenv : {C : KState} {X : VType} {Σ : Sig}
      → Γ ∷ gnd C ⊢K: X ↯ Σ , C
      ---------------------------
      → Γ ⊢K: X ↯ Σ , C

    setenv : {C : KState} {X : VType} {Σ : Sig}
      → Γ ⊢V: gnd C
      → Γ ⊢K: X ↯ Σ , C
      -------------------------
      → Γ ⊢K: X ↯ Σ , C

    user_finally : {Σ : Sig} {C : KState} {X Y : VType}
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      --------------------------
      → Γ ⊢K: Y ↯ Σ , C
      

infix 1 _⊢M:_ _⊢K:_ _⊢V:_ 
