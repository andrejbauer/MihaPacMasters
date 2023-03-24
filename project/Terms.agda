open import Parameters

module Terms where 
   
open import Types 
open import Contexts 
 
open GTypes G
open Ops O
 
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
 
    funM : {X : VType} {U : UType}
         → Γ ∷ X ⊢M: U
         ---------------------
         → Γ ⊢V: X ⟶ᵤ U
    
    funK : {X : VType} {K : KType}
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
 
    `let_`in : {X Y : VType} { Σ : Sig }
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ⊢M: Y ! Σ
      ----------
      → Γ ⊢M: Y ! Σ
 
    match_`with : {X Y : VType} {U : UType}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢M: U
      ----------------------------
      → Γ ⊢M: U
 
    `using_at_`run_finally : {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → Γ ⊢V: Σ ⇒ Σ' , C
      → Γ ⊢V: gnd C
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ∷ gnd C ⊢M: Y ! Σ'
      -----------------
      → Γ ⊢M: Y ! Σ'
 
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
 
    _∘_ : {X : VType} {K : KType}
      → Γ ⊢V: X ⟶ₖ K
      → Γ ⊢V: X
      ---------------------------------
      → Γ ⊢K: K
 
    `let_`in : {X Y : VType} {Σ : Sig} {C : KState}
      → Γ ⊢K: X ↯ Σ , C
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      ---------------------------
      → Γ ⊢K: Y ↯ Σ , C
 
    match_`with : {X Y : VType} {K : KType}
      → Γ ⊢V: X × Y
      → Γ ∷ X ∷ Y ⊢K: K
      ---------------------
      → Γ ⊢K: K
 
    -- TODO: fix!
 
    opₖ : {X Y : VType} {Σ : Sig} {C : KState}
      → (op : Op)
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
 
    user_`with : {Σ : Sig} {C : KState} {X Y : VType}
      → Γ ⊢M: X ! Σ
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      --------------------------
      → Γ ⊢K: Y ↯ Σ , C
      
 
infix 1 _⊢M:_ _⊢K:_ _⊢V:_ 
