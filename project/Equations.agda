open import Parameters

module Equations where --(G : GTypes) (O : Ops G) where

open import Types -- G O
open import Terms -- G O
open import Contexts -- G O
open import Replace -- G O

open GTypes G
open Ops O

interleaved mutual
 
  data _⊢V_≡_ (Γ : Ctx) : {X : VType} → Γ ⊢V: X → Γ ⊢V: X → Set
  data _⊢M_≡_ (Γ : Ctx) : {UU : UType} → Γ ⊢M: UU → Γ ⊢M: UU → Set
  data _⊢K_≡_ (Γ : Ctx) : {KK : KType} → Γ ⊢K: KK → Γ ⊢K: KK → Set

  data _⊢V_≡_ where

    -- equivalence rules

    refl : {X : VType} {V : Γ ⊢V: X}
         ---------------------------
         → Γ ⊢V V ≡ V

    sym : {X : VType} {V  V' : Γ ⊢V: X}
      → Γ ⊢V V ≡ V'
      --------------------
      → Γ ⊢V V' ≡ V

    trans : {X : VType} { V W Z : Γ ⊢V: X}
      → Γ ⊢V V ≡ W
      → Γ ⊢V W ≡ Z
      --------------------------
      → Γ ⊢V V ≡ Z

    -- congruence rules

    fun-cong :
        {X : VType} {U : UType}
        {M N : Γ ∷ X ⊢M: U}
      → (Γ ∷ X) ⊢M M ≡ N
      -------------------------
      → Γ ⊢V (fun M) ≡ (fun N)

    funK-cong :
      {X : VType} {K : KType}
      {M N : (Γ ∷ X) ⊢K: K}
      → (Γ ∷ X) ⊢K M ≡ N
      -----------------
      → Γ ⊢V funK M ≡ (funK N)

    runner-cong :
      {X : VType} {Σ Σ' : Sig} {C : KState}
      {R R' : ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op)}
      → ((op : Op) → (p : op ∈ₒ Σ) → (Γ ∷ gnd (param op)) ⊢K R op p ≡ R' op p)
      ------------------------------------------------------------------------
      → Γ ⊢V runner R ≡ runner R'

    -- rules from the paper


    unit-η : {V : Γ ⊢V: gnd unit}
           ----------------------
           → Γ ⊢V V ≡ ⟨⟩

    fun : {X : VType}
      → {!!}
      ------------
      → Γ ⊢V {!!} ≡ {!!}

    funK : {X : VType}
      → {!!}
      ---------------
      → Γ ⊢V {!!} ≡ {!!}

    
    

  data _⊢M_≡_ where

    -- equivalence rules
    refl : {X : UType} {M : Γ ⊢M: X}
         ---------------------------
         → Γ ⊢M M ≡ M

    sym : {X : UType} {M  M' : Γ ⊢M: X}
      → Γ ⊢M M ≡ M'
      --------------------
      → Γ ⊢M M' ≡ M

    trans : {X : UType} { M N O : Γ ⊢M: X}
      → Γ ⊢M M ≡ N
      → Γ ⊢M N ≡ O
      --------------------------
      → Γ ⊢M M ≡ O
    -- congruence rules

    return-cong :
      {X : VType}
      → {!!}
      ------------------
      → Γ ⊢M {!!} ≡ {!!}

    ∘-cong :
      {X : VType}
      → {!!}
      ----------------------
      → Γ ⊢M {!!} ≡ {!!}

    opₘ-cong :
      {X : VType}
      → {!!}
      --------------------
      → Γ ⊢M {!!} ≡ {!!}

    TryWith-cong :
      {X : VType}
      → {!!}
      --------------------
      → Γ ⊢M {!!} ≡ {!!}

    MatchWith-cong :
      {X : VType}
      → {!!}
      ----------------------
      → Γ ⊢M {!!} ≡ {!!}


    UsingAtRunFinally-cong :
      {X : VType}
      → {!!}
      ------------------------
      → Γ ⊢M {!!} ≡ {!!}

    KernelAtFinally-cong :
      {X : VType}
      → {!!}
      ------------------------
      → Γ ⊢M {!!} ≡ {!!}

    -- rules from the paper
    funM : {X : VType} {U : UType}
      → (funM : (Γ ∷ X) ⊢M: U)
      → Γ ⊢M {!!} ≡ {!!}

    TryReturn_With_ : {X Y : VType} {Σ : Sig}  {U : UType} {V : Γ ⊢M: U}
      → (V : Γ ⊢V: X)
      → (N : Γ ∷ X ⊢M: Y ! Σ)
      ----------------------------
      → Γ ⊢M Try (return V) With N ≡ {!N[V/x]!}

    let-beta-op : {X Y : VType} {Σ : Sig} {V : VType}            -- TODO: naming conventions, e.g., let-beta-op
      → (op : Op)
      → (V : Γ ⊢V: gnd (param op))
      → (M : Γ ∷ gnd (result op) ⊢M: X ! Σ)
      → (N : Γ ∷ X ⊢M: Y ! Σ)
      --------------------------------
      → Γ ⊢M Try (opᵤ op V M) With N
           ≡ opᵤ op V (Try M With (N [ wkᵣ ∘ᵣ exchᵣ ]ᵤᵣ))

    Matchprod_With : {X Y : VType} {U : UType} {V : Γ ⊢M: U}
      → (XxY : Γ ⊢V: X × Y)
      → (W : Γ ∷ X ∷ Y ⊢M: U)
      -----------------
      → Γ ⊢M (Match XxY With W) ≡ {!!} -- Unsure
      
    Matchnull_With : {X Y : VType} {U V : UType} {V : Γ ⊢M: U}
      → (XxY : Γ ⊢V: X × Y)
      → (B : Γ ⊢M: U)
      -----------------
      → Γ ⊢M  (Match XxY With {!!}) ≡ B -- Unsure

    Usingreturn_Run_Finally :{U V W : VType} 
      → {!Γ ⊢V: !}
      → {!!}
      → {!!}
      ------------
      → Γ ⊢M Using {!!} At {!!} Run (return {!!}) Finally (return {!!}) ≡ {!!}

    Usingop_Run_Finally :{U V W : VType} 
      → {!Γ ⊢V: !}
      → {!!}
      → {!!}
      ------------
      → Γ ⊢M Using {!!} At {!!} Run (return {!!}) Finally (return {!!}) ≡ {!!}

    Kernelreturn_At_Finally : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢M Kernel (return {!!}) At {!!} Finally (return {!!}) ≡ {!!}

    Kernelgetenv_At_Finally : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢M Kernel getenv {!!} At {!!} Finally (return {!!})
      ≡ Kernel {!!} At {!!} Finally (return {!!})

    Kernelsetenv_At_Finally : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢M Kernel setenv {!!} {!!} At {!!} Finally (return {!!})
      ≡ Kernel {!!} At {!!} Finally (return {!!})

    Kernelop_At_Finally : {X : VType}
      → (op : Op)
      → {!!}
      -------------------
      → Γ ⊢M Kernel opₖ {!!} {!!}  At {!!} Finally (return {!!})
      ≡ opᵤ op {!!} {!!}


    TryM_With : {X : VType}    -- let-eta
      → {!!}
      -------------------
      → Γ ⊢M {!!} ≡ {!!}
      
  data _⊢K_≡_ where

    -- equivalence rules
    refl : {X : KType} {K : Γ ⊢K: X}
         ---------------------------
         → Γ ⊢K K ≡ K

    sym : {X : KType} {K  K' : Γ ⊢K: X}
      → Γ ⊢K K ≡ K'
      --------------------
      → Γ ⊢K K' ≡ K

    trans : {X : KType} { K L M : Γ ⊢K: X}
      → Γ ⊢K K ≡ L
      → Γ ⊢K L ≡ M
      --------------------------
      → Γ ⊢K K ≡ M
    -- congruence rules

    return-cong :
      {X : VType}
      → {!!}
      ----------------
      → Γ ⊢K {!!} ≡ {!!}

    TryWith-cong :
      {X : VType}
      → {!!}
      ----------------
      → Γ ⊢K {!!} ≡ {!!}

    MatchWith-cong :
      {X : VType}
      → {!!}
      ----------------
      → Γ ⊢K {!!} ≡ {!!}

    opₖ-cong :
      {X : VType}
      → {!!}
      ----------------
      → Γ ⊢K {!!} ≡ {!!}

    getenv-cong :
      {X : VType}
      → {!!}
      -----------------
      → Γ ⊢K {!!} ≡ {!!}

    setenv-cong :
      {X : VType}
      → {!!}
      --------------------
      → Γ ⊢K {!!} ≡ {!!}

    UserWith-cong :
      {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K {!!} ≡ {!!}


    -- rules from the paper

    funK : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K {!!} ≡ {!!}

    TryReturn_With_ : {X : VType}
      → {!!}
      -----------------
      → Γ ⊢K Try {!!} With {!!} ≡ {!!}

    Tryop_With_ : {X : VType}
      → {!!}
      -----------------
      → Γ ⊢K Try opₖ {!!} {!!} With {!!} ≡ opₖ {!!} {!!}

    Trygetenv_With_ : {X : VType}
      → {!!}
      -----------------
      → Γ ⊢K Try getenv {!!} With {!!} ≡ getenv {!!}
    
    Trysetenv_With_ : {X : VType}
      → {!!}
      -----------------
      → Γ ⊢K Try setenv {!!} {!!} With {!!} ≡ setenv {!!} {!!}
      
    Matchprod_With : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K Match {!!} With {!!} ≡ {!!}
      
    Matchnull_With : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K Match {!!} With {!!} ≡ {!!}

    Userreturn_With : {X : VType}
      → {!!}
      ----------------------
      → Γ ⊢K User {!!} With {!!} ≡ {!!}

    Userop_With : {X : VType}
      → {!!}
      ----------------------
      → Γ ⊢K User {!!} With {!!} ≡ {!!}

    TryK_With : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K {!!} ≡ {!!}

    GetSetenv : {C : KState} {X : VType} {Σ : Sig} {K : Γ ⊢K: X ↯ Σ , C}
      → (A : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (V : Γ ⊢V: gnd C)
      -------------
      → Γ ⊢K setenv V (getenv A) ≡ K -- Unsure

    SetGetenv : {C : KState} {X : VType} {Σ : Sig} {K : Γ ⊢K: X ↯ Σ , C}
      → {!!}
      → {!!}
      --------------
      → Γ ⊢K setenv {!!} (getenv {!!}) ≡ setenv {!!} {!!}
      
    SetSetenv : {C C' : KState} {X : VType} {Σ : Sig} {K : Γ ⊢K: X ↯ Σ , C}
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ⊢V: gnd C)
      --------------
      → Γ ⊢K setenv V (setenv W K) ≡ setenv W K

    GetOpEnv : {X : VType}
      → {!!}
      -----------------
      → Γ ⊢K {!!} ≡ {!!}

    SetOpEnv : {X : VType}
      → {!!}
      ----------------
      → Γ ⊢K {!!} ≡ {!!}


