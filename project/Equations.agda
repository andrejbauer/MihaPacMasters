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

    rename-cooper-cong :
      {X : VType} {Σ Σ' : Sig} {C : KState}
      {R R' : ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op)}
      → ((op : Op) → (p : op ∈ₒ Σ) → (Γ ∷ gnd (param op)) ⊢K R op p ≡ R' op p)
      ------------------------------------------------------------------------
      → Γ ⊢V rename-cooper R ≡ rename-cooper R'

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
      (V₁ : Γ ⊢V: X)
      (V₂ : Γ ⊢V: Y)
      -- → (V : Γ ⊢V: X × Y) -- {! ⟨ ? , ? ⟩ !}) --(V : Γ ⊢V: X × Y)
      → (M : Γ ∷ X ∷ Y ⊢U: U)
      -----------------
      → Γ ⊢U match ⟨ V₁ , V₂ ⟩ `with M ≡ (M [ ((idₛ ∷ₛ V₁) ∷ₛ V₂) ]ᵤ)
  -- → Γ ⊢U match V `with M ≡  ? --(M [ (idₛ ∷ₛ {!   !}) ∷ₛ {!   !} ]ᵤ) --(M [ {!   !} ∷ₛ {!   !} ]ᵤ) -- Is it renaming or substitution here?
    --→ Γ ⊢U (Match XxY With W) ≡ {!!} -- Unsure

    match-with-beta-null : {U : UType} --{X : VType} {U : UType}
      -- → (V : Γ ⊢V: X)
      → (B : Γ ⊢U: U)
      -----------------
      → Γ ⊢U match ⟨ ⟨⟩ , ⟨⟩ ⟩ `with (B [ (wkₛ (wkₛ idₛ)) ]ᵤ) ≡ B  -- This might be correct but it feels wrong to write ⟨ ⟨⟩ , ⟨⟩ ⟩ as an empty set
      --→ Γ ⊢U  (Match XxY With {!!}) ≡ B -- Unsure

    using-run-finally-beta-return :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (V : Γ ⊢V: Σ ⇒ Σ' , C)
      → (W : Γ ⊢V: gnd C)
      → (V' : Γ ⊢V: X)
      → (F : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ') 
      → (N : Γ ⊢U: Y ! Σ')
      ------------
      → Γ ⊢U `using V at W `run return V' finally F ≡ (N [ idₛ ]ᵤ)
      --→ Γ ⊢U Using {!!} At {!!} Run (return {!!}) Finally (return {!!}) ≡ {!!}

    using-run-finally-beta-op :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (V : Γ ⊢V: Σ ⇒ Σ' , C)
      → (W : Γ ⊢V: gnd C)
      → (V' : Γ ⊢V: X)
      → (op : Op)
      → (Vₒ : Γ ⊢V: gnd (param op))
      → (p : op ∈ₒ {!   !})
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (F : {!   !} ⊢U: {!   !} ! {!   !})
      → (W : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: {!   !})
      ------------
      → Γ ⊢U `using V at W `run (opᵤ op p Vₒ M) finally (F [ {!   !} ]ᵤ) --(F [ wkₛ (wkₛ idₛ) ]ᵤ)
          ≡ kernel K at W finally (`using {!   !} at {!   !} `run {!   !} finally (F [ {!   !} ]ᵤ))
--→ Γ ⊢U Using {!!} At {!!} Run (return {!!}) Finally (return {!!}) ≡ {!!}

    kernel-at-finally-beta-return : {X : VType}
      {Σ Σ' : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (W : Γ ⊢V: gnd C)
      -------------------
      → Γ ⊢U kernel return V at W finally {!!} ≡ {!!}

    kernel-at-finally-beta-getenv : {X Y : VType}
      {Σ Σ' : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (W : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd C ⊢K: Y ↯ Σ , C)
      -------------------
      → Γ ⊢U kernel getenv K at W finally {!!}
          ≡ kernel {!!} at W finally {!!}

    kernel-at-finally-setenv : {X Y : VType}
      {Σ Σ' : Sig} {C : KState}
      → (V W : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: Y ↯ Σ , C)
      -------------------
      → Γ ⊢U kernel setenv V K at W finally {!!}
          ≡ kernel K at V finally {!!}

    kernel-at-finally-beta-op : {X : VType}
      {Σ : Sig}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → {!!}
      -------------------
      → Γ ⊢U kernel (opₖ op {!p!} {!!} {!!}) at {!!} finally {!!} ≡ {!!}


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

    opₖ-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {op : Op}
      {V₁ V₂ : Γ ⊢V: X}
      {K₁ K₂ : Γ ∷ Y ⊢K: X ↯ Σ , C}
      → Γ ⊢V V₁ ≡ V₂
      → Γ ∷ Y ⊢K K₁ ≡ K₂
      ----------------
      → Γ ⊢K opₖ op {!!} {! V₁ !} {! K₁ !} ≡ opₖ op {!!} {! V₂ !} {! K₂ !}

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
      → Γ ⊢K (funK K) ∘ V ≡ (K [ {!!} ]ₖ)

    let-in-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (G : Γ ∷ X ⊢K: Y ↯ Σ , C)
      → (L : Γ ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (return V) `in G ≡ (L [ {!!} ]ₖ)

    let-in-beta-op :
      {X Y Z : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (V : Γ ⊢V: X)
      → (K : Γ ∷ Y ⊢K: {!!} ↯ Σ , C)
      → (G : Γ ∷ X ⊢K: {!!} ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (opₖ op {!!} {! V !} {!!}) `in {!!}
          ≡ opₖ op {!!} {! V !} (`let {!!} `in {!G!})

    let-in-beta-getenv : {X Y : VType}
      {C : KState} {Σ : Sig}
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (G : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (getenv K) `in G
          ≡ getenv (`let K `in {!!})

    let-in-beta-setenv : {X : VType}
      → {!!}
      -----------------
      → Γ ⊢K `let (setenv {!!} {!!}) `in {!!}
          ≡ setenv {!!} (`let {!!} `in {!!})

    match-with-beta-prod : {X Y : VType}
      {G : KType}
      → (V : Γ ⊢V: X)
      → (W : Γ ⊢V: Y)
      → (K' : Γ ∷ X ∷ Y ⊢K: G)
      → (K : Γ ⊢K: G)
      -------------------
      → Γ ⊢K match ⟨ V , W ⟩ `with K' ≡ (K [ {!!} ]ₖ)

    match-with-beta-null : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K {!!} ≡ {!!}

    user-with-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (M : Γ ⊢U: X ! Σ)
      → (G : Γ ∷ X ⊢K: Y ↯ Σ , C)
      ----------------------
      → Γ ⊢K user return V `with G ≡ {!!}

    user-with-beta-op : {X Y : VType}
      (Σ : Sig) (C : KState)
      → (op : Op)
      → (V : Γ ⊢V: gnd (param op))
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (G : Γ ∷ X ⊢K: {!!} ↯ Σ , C)
      ----------------------
      → Γ ⊢K user (opᵤ op {!!} V M) `with G
          ≡ opₖ op {!!} V {!!}

    let-in-eta-K : {X : VType}
      {Σ : Sig} {C : KState}
      → (K : Γ ⊢K: X ↯ Σ , C)
      -------------------
      → Γ ⊢K `let K `in (return (var here)) ≡ K -- Also a questionable use of crtl-a

    GetSetenv : {C : KState} {X : VType} {Σ : Sig}
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (V : Γ ⊢V: gnd C)
      -------------
      → Γ ⊢K setenv V (getenv K) ≡ {!!}

    SetGetenv : {C : KState} {X : VType} {Σ : Sig}
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd C ⊢K: {!!} ↯ Σ , C)
      --------------
      → Γ ⊢K setenv V (getenv K) ≡ setenv V {!!}

    SetSetenv : {C C' : KState} {X : VType} {Σ : Sig}
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: X ↯ Σ , C)
      --------------
      → Γ ⊢K setenv V (setenv W K) ≡ setenv W K

    GetOpEnv : {X Y : VType}{C  : KState} {Σ Σ' : Sig}
      → (op : Op)
      → (V : Γ ∷ gnd C ⊢V: X)
      → (K : Γ ∷ gnd C ∷ Y ⊢K: X ↯ Σ' , C)
      -----------------
      → Γ ⊢K getenv (opₖ op {!!} {! V !} {! K !})
          ≡ opₖ op {!!} {!!} {!!}

    SetOpEnv : {X Y : VType}{C  : KState} {Σ Σ' : Sig}
      → (op : Op)
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ∷ gnd C ⊢V: X)
      → (K : Γ ∷ gnd C ∷ Y ⊢K: X ↯ Σ' , C)
      ----------------
      → Γ ⊢K setenv W (opₖ op {!!} {!!} {!!}) ≡ {!!}


infix 1 _⊢V_≡_ _⊢U_≡_ _⊢K_≡_
