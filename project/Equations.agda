open import Parameters

module Equations (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open import Types G O
open import Terms G O
open import Contexts G O

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
    
    -- rules from the paper


    unit-η : {V : Γ ⊢V: gnd unit}
           ----------------------
           → Γ ⊢V V ≡ ⟨⟩

    

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
    -- rules from the paper


    comp1 : {X : VType} {Σ : Sig} {V : Γ ⊢M: X ! Σ}
      → Γ ⊢M V ≡ {!!}

    ′try_′with : {X Y : VType} {U : UType} {V : Γ ⊢M: U}
      → Γ ⊢M {!!} ≡ {!!}

    ′match_′with : {X Y : VType} {U : UType} {V : Γ ⊢M: U}
      → (XxY : Γ ⊢V: X × Y)
      → (W : Γ ∷ X ∷ Y ⊢M: U)
      -----------------
      → Γ ⊢M matchpair XxY W ≡ {!!} -- Unsure
      
    ′match_′withnull : {X Y : VType} {U V : UType} {V : Γ ⊢M: U}
      → (XxY : Γ ⊢V: X × Y)
      → {!!}
      -----------------
      → Γ ⊢M matchpair XxY {!!} ≡ {!!} -- Unsure

    ′using_′run_′finally : {!!}
      → {!!}
      → {!!}
      → {!!}
      ------------
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
    -- rules from the paper

    getsetenv : {C : KState} {X : VType} {Σ : Sig} {K : Γ ⊢K: X ↯ Σ , C}
      → (A : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (V : Γ ⊢V: gnd C)
      -------------
      → Γ ⊢K setenv V (getenv A) ≡ K -- Unsure

    setgetenv : {C : KState} {X : VType} {Σ : Sig} {K : Γ ⊢K: X ↯ Σ , C}
      → {!!}
      → {!!}
      --------------
      → Γ ⊢K setenv {!!} (getenv {!!}) ≡ setenv {!!} {!!}
      
    setsetenv : {C C' : KState} {X : VType} {Σ : Sig} {K : Γ ⊢K: X ↯ Σ , C}
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ⊢V: gnd C)
      --------------
      → Γ ⊢K setenv V (setenv W K) ≡ setenv W K

metch_weth_ : {Γ : Ctx} {X Y : VType} {U V : UType} {V : Γ ⊢M: U} → {!!} → {!!} → Γ ⊢M {!!} ≡ {!!}
