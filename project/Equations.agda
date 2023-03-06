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

    -- congruence rules
    
    -- rules from the paper

    unit-η : {V : Γ ⊢V: gnd unit}
           ----------------------
           → Γ ⊢V V ≡ ⟨⟩

  data _⊢M_≡_ where

    -- equivalence rules
    -- congruence rules
    -- rules from the paper

  data _⊢K_≡_ where

    -- equivalence rules
    -- congruence rules
    -- rules from the paper


