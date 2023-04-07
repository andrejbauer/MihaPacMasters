{-# OPTIONS --allow-unsolved-metas #-}

open import Parameters

module Renaming where

open import Types
open import Terms
open import Contexts

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
(ρ ∘ᵣ ρ') p = ρ' (ρ p)

-- weakening renaming

wkᵣ : ∀ {Γ X} → Ren (Γ ∷ X) Γ
wkᵣ x =  there x

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
  (funM M) [ ρ ]ᵥᵣ = funM (M [ {!ρ!} ]ᵤᵣ)
  (funK K) [ ρ ]ᵥᵣ = {!!}
  runner R [ ρ ]ᵥᵣ = {!!}
  -- User
  sub-user M x [ ρ ]ᵤᵣ = sub-user (M [ ρ ]ᵤᵣ) x
  return V [ ρ ]ᵤᵣ = return (V [ ρ ]ᵥᵣ)
  (V₁ ∘ V₂) [ ρ ]ᵤᵣ = (V₁ [ ρ ]ᵥᵣ) ∘ (V₂ [ ρ ]ᵥᵣ)
  opᵤ op p V M [ ρ ]ᵤᵣ = opᵤ op p (V [ ρ ]ᵥᵣ) (M [ {!!} ]ᵤᵣ)
  `let M `in N [ ρ ]ᵤᵣ = `let M [ ρ ]ᵤᵣ `in {!!}
  (match x `with M) [ ρ ]ᵤᵣ = {!!}
  `using x at x₁ `run M finally M₁ [ ρ ]ᵤᵣ = {!!}
  kernel x at x₁ finally M [ ρ ]ᵤᵣ = {!!}
  -- Kernel
  K [ ρ ]ₖᵣ = {!!}

-- ...
