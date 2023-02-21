{-# OPTIONS --allow-unsolved-metas #-}

open import Types
open import  Agda.Builtin.Bool
-- To do, add Agda Standard Library
module Contexts where

_⊆_ : ? → ? → ?
A ⊆ A = ? --Temporary

data _⊢_ : VType → VType

sub-ground : {A : VType}
           --------------------------
           → A ⊑ A

sub-runner : {Σ₁ , Σ₂ , Σ′₁ , Σ′₂ : Sig} →
                      {C , C′ : Ker} →
                      Σ′₁ ⊆ Σ₁ →
                      Σ₂ ⊆ Σ′₂ →
                      --C ≡ C′ →
                      ---------------------
                      Σ₁ ⇒ [ Σ₂ , C ] ⊑ Σ′₁ ⇒ [ Σ′₂ , C′ ]

sub-kernel : {X , X′ : Ctx} →
                     {Σ , Σ′ : Sig} →
                     {C , C′ : Ker} →
                     X ⊑ X′ →
                     Σ ⊑ Σ′ →
                     --C ≡ C′ →
                     -----------
                     X ↯ [ Σ , C ] ⊑ X′ ↯ [ Σ′ , C′ ]

--tyuser-try : 
                      
          
