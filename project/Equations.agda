open import Parameters

module Equations where

open import Types
open import Terms
open import Contexts
open import Renaming
open import Substitution


open GTypes G
open Ops O

interleaved mutual

  data _⊢V_≡_ (Γ : Ctx) : {X : VType} → Γ ⊢V: X → Γ ⊢V: X → Set
  data _⊢U_≡_ (Γ : Ctx) : {UU : UType} → Γ ⊢U: UU → Γ ⊢U: UU → Set
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

    prod-cong :
      {X Y : VType}
      {V₁ V₂ : Γ ⊢V: X}
      {W₁ W₂ : Γ ⊢V: Y}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ⊢V W₁ ≡ W₂
      -----------------------------
      → Γ ⊢V ⟨ V₁ , W₁ ⟩ ≡ ⟨ V₂ , W₂ ⟩

    fun-cong :
        {X : VType} {U : UType}
        {M N : Γ ∷ X ⊢U: U}
      → (Γ ∷ X) ⊢U M ≡ N
      -------------------------
      → Γ ⊢V (funM M) ≡ (funM N)

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


    unit-eta : {V : Γ ⊢V: gnd unit}
           ----------------------
           → Γ ⊢V V ≡ ⟨⟩

    funM-eta : {X : VType} {U : UType} --funU-eta
      {V : Γ ⊢V: X ⟶ᵤ U}
      ------------
      → Γ ⊢V funM ((V [ wkᵣ ]ᵥᵣ) ∘ var here) ≡ V -- str 32 fig 12 druga enačba v prvi vrstici

    funK-eta : {X : VType} {K : KType}
      {V : Γ ⊢V: X ⟶ₖ K}
      ---------------
      → Γ ⊢V funK ((V [ wkᵣ ]ᵥᵣ) ∘ (var here)) ≡ V




  data _⊢U_≡_ where

    -- equivalence rules
    refl : {X : UType} {M : Γ ⊢U: X}
         ---------------------------
         → Γ ⊢U M ≡ M

    sym : {X : UType} {M  M' : Γ ⊢U: X}
      → Γ ⊢U M ≡ M'
      --------------------
      → Γ ⊢U M' ≡ M

    trans : {X : UType} { M N O : Γ ⊢U: X}
      → Γ ⊢U M ≡ N
      → Γ ⊢U N ≡ O
      --------------------------
      → Γ ⊢U M ≡ O
    -- congruence rules

    return-cong :
      {X : VType} {V W : Γ ⊢V: X}
      → Γ ⊢V V ≡ W
      ------------------
      → Γ ⊢U return V ≡ return W

    ∘-cong :
      {X : VType} {U : UType}
      {V₁ V₂ : Γ ⊢V: X ⟶ᵤ U}
      {W₁ W₂ : Γ ⊢V: X}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ⊢V W₁ ≡ W₂
      ----------------------
      → Γ ⊢U V₁ ∘ W₁ ≡ (V₂ ∘ W₂)

    opᵤ-cong :
      {X : VType} {Σ : Sig}
      {op : Op}
      {V₁ V₂ : Γ ⊢V: gnd (param op)}
      {M₁ M₂ : Γ ∷ gnd (result op) ⊢U: X ! Σ}
      → (p : op ∈ₒ Σ)
      → Γ ⊢V V₁ ≡ V₂
      → (Γ ∷ gnd (result op)) ⊢U M₁ ≡ M₂
      --------------------
      → Γ ⊢U opᵤ op p  V₁ M₁ ≡ opᵤ op p V₂ M₂

    let-in-cong :
      {X Y : VType} {Σ : Sig}
      {M₁ M₂ : Γ ⊢U: X ! Σ}
      {N₁ N₂ : Γ ∷ X ⊢U: Y ! Σ}
      → Γ ⊢U M₁ ≡ M₂
      → Γ ∷ X ⊢U N₁ ≡ N₂
      --------------------
      → Γ ⊢U `let M₁ `in N₁ ≡ `let M₂ `in N₂

    match-with-cong :
      {X Y : VType} {U : UType}
      {V₁ V₂ : Γ ⊢V: X × Y}
      {M₁ M₂ : Γ ∷ X ∷ Y ⊢U: U}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ∷ X ∷ Y ⊢U M₁ ≡ M₂
      ----------------------
      → Γ ⊢U (match V₁ `with M₁) ≡ (match V₂ `with M₂)


    using-at-run-finally-cong :
      {X Y : VType} {Σ Σ' : Sig} {C : KState}
      {V₁ V₂ : Γ ⊢V: Σ ⇒ Σ' , C}
      {W₁ W₂ : Γ ⊢V: gnd C}
      {M₁ M₂ : Γ ⊢U: X ! Σ}
      {N₁ N₂ : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ'}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ⊢V W₁ ≡ W₂
      → Γ ⊢U M₁ ≡ M₂
      → Γ ∷ X ∷ gnd C ⊢U N₁ ≡ N₂
      ------------------------
      → Γ ⊢U `using V₁ at W₁ `run M₁ finally N₁
      ≡ `using V₂ at W₂ `run M₂ finally N₂

    kernel-at-finally-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {K₁ K₂ : Γ ⊢K: X ↯ Σ , C}
      {V₁ V₂ : Γ ⊢V: gnd C}
      {M₁ M₂ : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ}
      → Γ ⊢K K₁ ≡ K₂
      → Γ ⊢V V₁ ≡ V₂
      → Γ ∷ X ∷ gnd C ⊢U M₁ ≡ M₂
      ------------------------
      → Γ ⊢U kernel K₁ at V₁ finally M₁ ≡ kernel K₂ at V₂ finally M₂

    -- rules from the paper
    funM-beta : {X : VType} {U : UType} -- str32 prva vrstica
      → (M : (Γ ∷ X) ⊢U: U)
      → (V : Γ ⊢V: X)
      -------------------------------
      → Γ ⊢U (funM M) ∘ V ≡ (M [ idₛ ∷ₛ V ]ᵤ)

    let-in-beta-return_ : {X Y : VType} {Σ : Sig}  {U : UType} {V : Γ ⊢U: U}
      → (V : Γ ⊢V: X)
      → (N : Γ ∷ X ⊢U: Y ! Σ)
      ----------------------------
      → Γ ⊢U `let (return V) `in N ≡ (N [ (idₛ ∷ₛ V) ]ᵤ)

    let-in-beta-op : {X Y : VType} {Σ : Sig} {V : VType}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (N : Γ ∷ X ⊢U: Y ! Σ)
      --------------------------------
      → Γ ⊢U `let (opᵤ op p V M) `in N ≡ opᵤ op p V (`let M `in (N [ (extendₛ (wkₛ idₛ)) ]ᵤ))

    match-with-beta-prod : {X Y : VType} {U : UType} {V : Γ ⊢V: X × Y} -- LOOK WITH A MORE CAREFUL LOOK AS I CHANGED THE V from being a usertype (for whatever reason) to a valuetype computation
      -- Bodi pazliv da ne zamenjas V1 in V2 na koncu
      (V₁ : Γ ⊢V: X)
      (V₂ : Γ ⊢V: Y)
      → (M : Γ ∷ X ∷ Y ⊢U: U)
      -----------------
      → Γ ⊢U match ⟨ V₁ , V₂ ⟩ `with M ≡ (M [ ((idₛ ∷ₛ V₁) ∷ₛ V₂) ]ᵤ)

{-     match-with-beta-null : {U : UType} -- Zaenkrat naj to ostane prazno
      → (V : Γ ⊢U: gnd 
      → (B : Γ ⊢U: U)
      -----------------
      → Γ ⊢U match ? `with (B [ (wkₛ (wkₛ idₛ)) ]ᵤ) ≡ B -}

    using-run-finally-beta-return :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (R : Γ ⊢V: Σ ⇒ Σ' , C)
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ⊢V: X)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ') 
      ------------
      → Γ ⊢U `using R at W `run return V finally N ≡ (N [ (idₛ ∷ₛ V) ∷ₛ W ]ᵤ)

    using-run-finally-beta-op :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (R : ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op))
      → (W : Γ ⊢V: gnd C)
      → (op : Op)
      → (V : Γ ⊢V: gnd (param op))
      → (p : op ∈ₒ Σ)
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ')
      ------------
      → Γ ⊢U `using runner R at W `run (opᵤ op p V M) finally N
          ≡ kernel R op p [ idₛ ∷ₛ V ]ₖ at W finally (`using (runner (rename-runner R (wkᵣ ∘ᵣ wkᵣ))) at var here `run M [ wkᵣ ]ᵤᵣ finally (N [ extdᵣ (extdᵣ (wkᵣ ∘ᵣ wkᵣ)) ]ᵤᵣ))
          
    kernel-at-finally-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (W : Γ ⊢V: gnd C)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel return V at W finally N ≡ (N [ ((idₛ ∷ₛ V) ∷ₛ W) ]ᵤ)

    kernel-at-finally-beta-getenv : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (W : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel getenv K at W finally N
          ≡ kernel K [ (idₛ ∷ₛ W) ]ₖ at W finally N

    kernel-at-finally-setenv : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V W : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: X ↯ Σ , C)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel setenv V K at W finally N
          ≡ kernel K at V finally N

    kernel-at-finally-beta-op : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (W : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel (opₖ op p V K) at W finally N ≡ opᵤ op p V (kernel K at (W [ (wkₛ idₛ) ]ᵥ) finally (N [ extendₛ (extendₛ (wkₛ idₛ)) ]ᵤ))


    let-in-eta-M : {X : VType}    -- let-eta
      {Σ : Sig}
      → (M : Γ ⊢U: X ! Σ)
      -------------------
      → Γ ⊢U `let M `in (return (var here)) ≡ M -- Questionable solution as I have no clue how it works

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
      {X : VType} {Σ : Sig} {C : KState}
      {V₁ V₂ : Γ ⊢V: X}
      → Γ ⊢V V₁ ≡ V₂
      ----------------
      → Γ ⊢K return V₁ ≡ return V₂

    ∘-cong :
      {X : VType} {K : KType}
      {V₁ V₂ : Γ ⊢V: X ⟶ₖ K}
      {W₁ W₂ : Γ ⊢V: X}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ⊢V W₁ ≡ W₂
      -----------------------
      → Γ ⊢K V₁ ∘ W₁ ≡ (V₂ ∘ W₂)

    let-in-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {K₁ K₂ : Γ ⊢K:  X ↯ Σ , C}
      {L₁ L₂ : Γ ∷ X ⊢K: Y ↯ Σ , C}
      → Γ ⊢K K₁ ≡ K₂
      → Γ ∷ X ⊢K L₁ ≡ L₂
      ----------------
      → Γ ⊢K `let K₁ `in L₁ ≡ `let K₂ `in L₂

    match-with-cong :
      {X Y : VType} {K : KType}
      {V₁ V₂ : Γ ⊢V: X × Y}
      {K₁ K₂ : Γ ∷ X ∷ Y ⊢K: K}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ∷ X ∷ Y ⊢K K₁ ≡ K₂
      ----------------
      → Γ ⊢K match V₁ `with K₁ ≡ (match V₂ `with K₂)

    opₖ-cong :  -- cong pravilo, poglej še enkrat če pravilno
      {X Y : VType} {Σ : Sig} {C : KState}
      {op : Op}
      {p : op ∈ₒ Σ}
      {V₁ V₂ : Γ ⊢V: gnd (param op)}
      {K₁ K₂ : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ∷ gnd (result op) ⊢K K₁ ≡ K₂
      ----------------
      → Γ ⊢K opₖ op p V₁ K₁ ≡ opₖ op p V₂ K₂

    getenv-cong :
      {X : VType} {C : KState} {Σ : Sig}
      {K₁ K₂ : Γ ∷ gnd C ⊢K: X ↯ Σ , C}
      → Γ ∷ gnd C ⊢K K₁ ≡ K₂
      -----------------
      → Γ ⊢K getenv K₁ ≡ getenv K₂

    setenv-cong :
      {X : VType} {C : KState} {Σ : Sig}
      {V₁ V₂ : Γ ⊢V: gnd C}
      {K₁ K₂ : Γ ⊢K: X ↯ Σ , C}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ⊢K K₁ ≡ K₂
      --------------------
      → Γ ⊢K setenv V₁ K₁ ≡ setenv V₂ K₂

    user-with-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {M₁ M₂ : Γ ⊢U: X ! Σ}
      {K₁ K₂ : Γ ∷ X ⊢K: Y ↯ Σ , C}
      → Γ ⊢U M₁ ≡ M₂
      → Γ ∷ X ⊢K K₁ ≡ K₂
      -------------------
      → Γ ⊢K user M₁ `with K₁ ≡ user M₂ `with K₂


    -- rules from the paper

    funK-beta : {X : VType} {L : KType}
      → (K : Γ ∷ X ⊢K: L)
      → (V : Γ ⊢V: X)
      -------------------
      → Γ ⊢K (funK K) ∘ V ≡ (K [ idₛ ∷ₛ V ]ₖ)

    let-in-beta-return : {X Y : VType} --preveri pozneje
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C )
      -----------------
      → Γ ⊢K `let (return V) `in L ≡ (L [ idₛ ∷ₛ V ]ₖ )

    let-in-beta-op :
      {X Y Z : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (K : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (opₖ op p V K) `in L ≡ opₖ op p V (`let K `in (L [ (extendₛ (wkₛ idₛ)) ]ₖ))

    let-in-beta-getenv : {X Y : VType} -- nisem povsem preprican tu
      {C : KState} {Σ : Sig}
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (getenv K) `in L
          ≡ getenv (`let K `in (L [ (extendₛ (wkₛ idₛ)) ]ₖ))

    let-in-beta-setenv : {X Y : VType}
      {C : KState} {Σ : Sig} 
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: X ↯ Σ , C)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C) 
      -----------------
      → Γ ⊢K `let (setenv V K) `in L
          ≡ setenv V (`let K `in L)

    match-with-beta-prod : {X Y Z : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (W : Γ ⊢V: Y)
      → (K : Γ ∷ X ∷ Y ⊢K: Z ↯ Σ , C)
      -------------------
      → Γ ⊢K match ⟨ V , W ⟩ `with K ≡ (K [ (idₛ ∷ₛ V) ∷ₛ W ]ₖ)

    {- match-with-beta-null : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K {!!} ≡ {!!} -}

    user-with-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C)
      ----------------------
      → Γ ⊢K user return V `with L ≡ (L [ (idₛ ∷ₛ V) ]ₖ)

    user-with-beta-op : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C)
      ----------------------
      → Γ ⊢K user (opᵤ op p V M) `with L
          ≡ opₖ op p V (user M `with (L [ extendₛ (wkₛ idₛ) ]ₖ))

    let-in-eta-K : {X : VType}
      {Σ : Sig} {C : KState}
      → (K : Γ ⊢K: X ↯ Σ , C)
      -------------------
      → Γ ⊢K `let K `in (return (var here)) ≡ K -- Also a questionable use of crtl-a

    GetSetenv : {C : KState} {X Y : VType} {Σ : Sig} --tudi za pogledati
      → (K : Γ ⊢K: X ↯ Σ , C)
      → (V : Γ ∷ gnd C ⊢V: gnd C)
      -------------
      → Γ ⊢K getenv (setenv V (K [ wkₛ idₛ ]ₖ)) ≡ K

    SetGetenv : {C : KState} {X : VType} {Σ : Sig}
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      --------------
      → Γ ⊢K setenv V (getenv K) ≡ setenv V (K [ idₛ ∷ₛ V ]ₖ)

    SetSetenv : {C C' : KState} {X : VType} {Σ : Sig}
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: X ↯ Σ , C)
      --------------
      → Γ ⊢K setenv V (setenv W K) ≡ setenv W K

    GetOpEnv : {X Y : VType}{C  : KState} {Σ : Sig} -- tu se zdi problematicno kar vtikati gnd notri, poglej pozneje
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (K : Γ ⊢K: X ↯ Σ , C)
      -----------------
      → Γ ⊢K getenv (opₖ op p (V [ wkₛ idₛ ]ᵥ) (K [ wkₛ (wkₛ idₛ) ]ₖ))
          ≡ opₖ op p V (getenv (K [ wkₛ (wkₛ idₛ) ]ₖ))

    SetOpEnv : {X Y : VType}{C  : KState} {Σ : Sig} -- Negotovost glede param op
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (K : Γ ⊢K: X ↯ Σ , param op)
      ----------------
      → Γ ⊢K setenv V (opₖ op p V (K [ wkₛ idₛ ]ₖ)) ≡ K


infix 1 _⊢V_≡_ _⊢U_≡_ _⊢K_≡_
         