{-# OPTIONS --allow-unsolved-metas #-}

open import Parameters

module Substitution where --(G : GTypes) (O : Ops G) where

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
ρ' ∘ᵣ ρ = λ z → ρ (ρ' z)
 
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
  -- Value
  var x [ ρ ]ᵥᵣ = var (ρ x)
  sub-value V x [ ρ ]ᵥᵣ = sub-value ( V [ ρ ]ᵥᵣ) x
  ⟨⟩ [ ρ ]ᵥᵣ = ⟨⟩
  ⟨ V , W ⟩ [ ρ ]ᵥᵣ = ⟨  V [ ρ ]ᵥᵣ , W [ ρ ]ᵥᵣ ⟩
  (fun x) [ ρ ]ᵥᵣ = fun {!wkᵣ!}
  (funK x) [ ρ ]ᵥᵣ = {!!}
  runner x [ ρ ]ᵥᵣ = {!!}
  -- User
  M [ ρ ]ᵤᵣ = {!!}
  {-ub-user M x [ ρ ]ᵤᵣ = sub-user (M [ ρ ]ᵤᵣ) x
  return V [ ρ ]ᵤᵣ = return (V [ ρ ]ᵥᵣ)
  (V ∘ W) [ ρ ]ᵤᵣ = (V [ ρ ]ᵥᵣ) ∘ (W [ ρ ]ᵥᵣ)
  opᵤ op V M [ ρ ]ᵤᵣ = opᵤ op (V [ ρ ]ᵥᵣ) (M [ {! !} ]ᵤᵣ)
  `let M `in N [ ρ ]ᵤᵣ = {!!}
  match x `with M [ ρ ]ᵤᵣ = {!!}
  `using x at x₁ `run M finally M₁ [ ρ ]ᵤᵣ = {!!}
  kernel x at x₁ finally M [ ρ ]ᵤᵣ = {!!} -}
  -- Kernel
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
