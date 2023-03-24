{-# OPTIONS --allow-unsolved-metas #-}

open import Parameters

module Substitution where 

open import Types 
open import Terms 
open import Contexts 
open import Renaming
 
open GTypes G
open Ops O

-- Type of substitutions
 
Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ' → Γ ⊢V: X
 
-- Action of substitutions
 
interleaved mutual
 
  _[_]ᵥ : ∀{Γ Γ' X} → Γ' ⊢V: X → Sub Γ Γ' → Γ ⊢V: X
  _[_]ᵤ : ∀{Γ Γ' X} → Γ' ⊢M: X → Sub Γ Γ' → Γ ⊢M: X
  _[_]ₖ : ∀{Γ Γ' X} → Γ' ⊢K: X → Sub Γ Γ' → Γ ⊢K: X
 
  var p [ σ ]ᵥ = σ p
  sub-value V p [ σ ]ᵥ = sub-value (V [ σ ]ᵥ) p
  ⟨⟩ [ σ ]ᵥ = ⟨⟩
  ⟨ V , W ⟩ [ σ ]ᵥ = ⟨ V [ σ ]ᵥ , W [ σ ]ᵥ ⟩
  (funM M) [ σ ]ᵥ = funM {!!}
  (funK K) [ σ ]ᵥ = funK (K [ {!!} ]ₖ)
  runner R [ σ ]ᵥ = runner {!R [ ? ]ᵥ!}
 
  sub-user M x [ σ ]ᵤ = sub-user (M [ σ ]ᵤ) x
  return V [ σ ]ᵤ = return (V [ σ ]ᵥ)
  (V₁ ∘ V₂) [ σ ]ᵤ = (V₁ [ σ ]ᵥ) ∘ (V₂ [ σ ]ᵥ)
  opᵤ op V M [ σ ]ᵤ = opᵤ op (V [ σ ]ᵥ) {!M [ σ ]ᵤ!}
  `let M `in N [ σ ]ᵤ = `let M [ σ ]ᵤ `in {!!}
  (match XxY `with M) [ σ ]ᵤ = match (XxY [ σ ]ᵥ) `with {!!}
  `using R at W `run M finally N [ σ ]ᵤ = `using R [ σ ]ᵥ at W [ σ ]ᵥ `run M [ σ ]ᵤ finally {!!}
  kernel K at W finally M [ σ ]ᵤ = kernel (K [ σ ]ₖ) at (W [ σ ]ᵥ) finally {!!}
  
  sub-kernel K p [ σ ]ₖ = sub-kernel (K [ σ ]ₖ) p
  return V [ σ ]ₖ = return (V [ σ ]ᵥ)
  (V₁ ∘ V₂) [ σ ]ₖ = (V₁ [ σ ]ᵥ) ∘ (V₂ [ σ ]ᵥ)
  `let K `in G [ σ ]ₖ = `let (K [ σ ]ₖ) `in {!!}
  (match V `with K) [ σ ]ₖ = match V [ σ ]ᵥ `with {!!}
  opₖ op V K [ σ ]ₖ = opₖ op (V [ σ ]ᵥ) {!!}
  getenv K [ σ ]ₖ = getenv {!!}
  setenv x K [ σ ]ₖ = {!!}
  user M `with K [ σ ]ₖ = user (M [ σ ]ᵤ) `with {!!}
