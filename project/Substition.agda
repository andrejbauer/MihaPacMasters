{-# OPTIONS --allow-unsolved-metas #-}

open import Parameters

module Replace where --(G : GTypes) (O : Ops G) where

open import Types -- G O
open import Terms -- G O
open import Contexts -- G O
 
open GTypes G
open Ops O
 
-- Type of renamings
 
Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : VType} → X ∈ Γ' → X ∈ Γ
 
-- identity renaming
 
idᵣ : ∀ {Γ} → Ren Γ Γ
idᵣ x = x
 
-- composition of renamings
 
_∘ᵣ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
ρ' ∘ᵣ ρ = {!!}
 
-- weakening renaming
 
wkᵣ : ∀ {Γ X} → Ren (Γ ∷ X) Γ
wkᵣ x = there x
 
-- exchange renaming
 
exchᵣ : ∀ {Γ X Y} → Ren (Γ ∷ X ∷ Y) (Γ ∷ Y ∷ X)
exchᵣ here = there here
exchᵣ (there here) = here
exchᵣ (there (there x)) = there (there x)
 
-- Action of renamings
 
interleaved mutual
 
  _[_]ᵥᵣ : ∀{Γ Γ' X} → Γ' ⊢V: X → Ren Γ Γ' → Γ ⊢V: X
  _[_]ᵤᵣ : ∀{Γ Γ' X} → Γ' ⊢M: X → Ren Γ Γ' → Γ ⊢M: X
  _[_]ₖᵣ : ∀{Γ Γ' X} → Γ' ⊢K: X → Ren Γ Γ' → Γ ⊢K: X
 
  V [ ρ ]ᵥᵣ = {!!}
  M [ ρ ]ᵤᵣ = {!!}
  K [ ρ ]ₖᵣ = {!!}
 
-- ...
 
-- Type of substitutions
 
Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ' → Γ ⊢V: X
 
-- Action of substitutions
 
interleaved mutual
 
  _[_]ᵥ : ∀{Γ Γ' X} → Γ' ⊢V: X → Sub Γ Γ' → Γ ⊢V: X
  _[_]ᵤ : ∀{Γ Γ' X} → Γ' ⊢M: X → Sub Γ Γ' → Γ ⊢M: X
  _[_]ₖ : ∀{Γ Γ' X} → Γ' ⊢K: X → Sub Γ Γ' → Γ ⊢K: X
 
  var x [ σ ]ᵥ = {!!}
  sub-value V p [ σ ]ᵥ = {!!}
  ⟨⟩ [ σ ]ᵥ = {!!}
  ⟨ V , W ⟩ [ σ ]ᵥ = ⟨ V [ σ ]ᵥ , W [ σ ]ᵥ ⟩
  (fun M) [ σ ]ᵥ = fun (M [ {!!} ]ᵤ)
  (funK K) [ σ ]ᵥ = {!!}
  runner R [ σ ]ᵥ = {!!}
 
  M [ σ ]ᵤ = {!!}
  
  K [ σ ]ₖ = {!!}
