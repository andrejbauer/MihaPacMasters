open import Parameters

module Terms where --(G : GTypes) (O : Ops G) where
   
open import Types -- G O
open import Contexts -- G O
 
open GTypes G
open Ops O
 
-- replaced ⦂ with ː because my computer's font does not show the former.
-- ː is \:3
-- Replaced ː with :, because I don't see the point
-- Well-typed value and computation terms
interleaved mutual
 
  data _⊢V:_ (Γ : Ctx) : VType → Set  
  data _⊢M:_ (Γ : Ctx) : UType → Set
  data _⊢K:_ (Γ : Ctx) : KType → Set
 
  -- Co-operations
  co-op : Ctx → Sig → KState → Op → Set
  co-op Γ Σ C op = Γ ∷ gnd (param op) ⊢K: gnd (result op) ↯ Σ , C
 
  data _⊢V:_ where
 
    var : {X : VType}
        → X ∈ Γ          -- constructively, exists a variable with type X in Γ
        -------------
        → Γ ⊢V: X
 
    sub-value : {X X' : VType}
        → Γ ⊢V: X
        → X ⊑ᵥ X'
        ------------------
        → Γ ⊢V: X'
 
    ⟨⟩ :
        --------------------
        Γ ⊢V: gnd unit
 
    ⟨_,_⟩ : {X Y : VType}
        → Γ ⊢V: X
        → Γ ⊢V: Y
        -------------------
        → Γ ⊢V: X × Y
 
    fun_ : {X : VType} {U : UType}
         → Γ ∷ X ⊢M: U
         ---------------------
         → Γ ⊢V: X ⟶ᵤ U
    
    funK_ : {X : VType} {K : KType}
         → (Γ ∷ X) ⊢K: K
         ------------------------------
         → Γ ⊢V: X ⟶ₖ K
 
    runner : {Σ Σ' : Sig} {C : KState} 
           → ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op)
           ---------------------------------------------
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
 
    _∘_ : {X : VType} {U : UType} -- Formerly apply
      → Γ ⊢V: X ⟶ᵤ U
      → Γ ⊢V: X
      -------------------------
      → Γ ⊢M: U
      
    opᵤ : {X : VType} {Σ : Sig}
       → (op : Op)
       → Γ ⊢V: gnd (param op)
       → Γ ∷ gnd (result op) ⊢M: X ! Σ
       -------------------------------
       → Γ ⊢M: X ! Σ
 
    -- TODO: lowercase constructor names, perhaps try_'with_
 
    -- TODO: rename to `let_`in_
 
    Try_With : {X Y : VType} { Σ : Sig }
    -- let x = M in N
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ⊢M: Y ! Σ
      ----------
      → Γ ⊢M: Y ! Σ
 
    Match_With_ : {X Y : VType} {U : UType}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢M: U
      ----------------------------
      → Γ ⊢M: U
 
   -- op : {Σ : Sig}
   --   → {!!}
 
    Using_At_Run_Finally : {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → Γ ⊢V: Σ ⇒ Σ' , C
      → Γ ⊢V: gnd C
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ∷ gnd C ⊢M: Y ! Σ'
      -----------------
      → Γ ⊢M: Y ! Σ'
 
    -- `using R at W run M finally N
    -- vs
    -- run R W M N
 
 
    Kernel_At_Finally :{X Y : VType} {Σ : Sig} {C : KState}
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
 
    _∘_ : {X : VType} {K : KType}
      → Γ ⊢V: X ⟶ₖ K
      → Γ ⊢V: X
      ---------------------------------
      → Γ ⊢K: K
 
    Try_With : {X Y : VType} {Σ : Sig} {C : KState}
      → Γ ⊢K: X ↯ Σ , C
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      ---------------------------
      → Γ ⊢K: Y ↯ Σ , C
 
    Match_With_ : {X Y : VType} {K : KType}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢K: K
      ---------------------
      → Γ ⊢K: K
 
    -- TODO: fix!
 
    opₖ : {X Y : VType} {Σ : Sig} {C : KState}
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
 
    User_With : {Σ : Sig} {C : KState} {X Y : VType}
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      --------------------------
      → Γ ⊢K: Y ↯ Σ , C
      
 
infix 1 _⊢M:_ _⊢K:_ _⊢V:_ 
