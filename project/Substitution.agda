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

-- Auxiliary functions for substitutions

-- note: we probably should generalize this so that the extra variable (of type `X`)
--       maps to a given term, not necessarily itself
-- TASK: implement this one as two simpler functions:
--       (1) σ : Sub Γ Γ' is transformed to σ' : Sub (Γ ∷ X) Γ'
--       (2) given τ : Sub Δ Δ' and Δ ⊢ v : X, we get ⟨τ, v⟩ : Sub Δ (Δ' ∷ X)
extend : ∀ {Γ Γ' X} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
extend σ here = var here
extend σ (there x) =  σ x [ wkᵣ ]ᵥᵣ

addₛ : ∀ {Γ Γ' X} → Sub Γ Γ' → Sub (Γ ∷ X) Γ'
addₛ σ here = {!wkᵣ σ!}
addₛ σ (there p) = {!!}

cont : Ctx → Ctx → Ctx -- concatenation
cont Γ [] = Γ
cont Γ (Δ ∷ X) = (cont Γ Δ) ∷ X

fun1 : ∀ {Γ Γ' X} → Sub Γ Γ' → Γ ⊢V: X → Sub Γ (Γ' ∷ X)
fun1 σ V here = V
fun1 σ V (there p) = σ p -- I do not understand what exactly happened here. It is a bad solution.

-- Action of substitutions

interleaved mutual

  _[_]ᵥ : ∀{Γ Γ' X} → Γ' ⊢V: X → Sub Γ Γ' → Γ ⊢V: X
  _[_]ᵤ : ∀{Γ Γ' X} → Γ' ⊢M: X → Sub Γ Γ' → Γ ⊢M: X
  _[_]ₖ : ∀{Γ Γ' X} → Γ' ⊢K: X → Sub Γ Γ' → Γ ⊢K: X

  var p [ σ ]ᵥ = σ p
  sub-value V p [ σ ]ᵥ = sub-value (V [ σ ]ᵥ) p
  ⟨⟩ [ σ ]ᵥ = ⟨⟩
  ⟨ V , W ⟩ [ σ ]ᵥ = ⟨ V [ σ ]ᵥ , W [ σ ]ᵥ ⟩
  (funM M) [ σ ]ᵥ = funM ( M [ extend σ ]ᵤ)
  (funK K) [ σ ]ᵥ = funK (K [ {!!} ]ₖ)
  runner R [ σ ]ᵥ = runner {!R [ ? ]ᵥ!}

  sub-user M x [ σ ]ᵤ = sub-user (M [ σ ]ᵤ) x
  return V [ σ ]ᵤ = return (V [ σ ]ᵥ)
  (V₁ ∘ V₂) [ σ ]ᵤ = (V₁ [ σ ]ᵥ) ∘ (V₂ [ σ ]ᵥ)
  opᵤ op p V M [ σ ]ᵤ = opᵤ op p (V [ σ ]ᵥ) {!M [ σ ]ᵤ!}
  `let M `in N [ σ ]ᵤ = `let M [ σ ]ᵤ `in {!!}
  (match XxY `with M) [ σ ]ᵤ = match (XxY [ σ ]ᵥ) `with {!!}
  `using R at W `run M finally N [ σ ]ᵤ = `using R [ σ ]ᵥ at W [ σ ]ᵥ `run M [ σ ]ᵤ finally {!!}
  kernel K at W finally M [ σ ]ᵤ = kernel (K [ σ ]ₖ) at (W [ σ ]ᵥ) finally {!!}

  sub-kernel K p [ σ ]ₖ = sub-kernel (K [ σ ]ₖ) p
  return V [ σ ]ₖ = return (V [ σ ]ᵥ)
  (V₁ ∘ V₂) [ σ ]ₖ = (V₁ [ σ ]ᵥ) ∘ (V₂ [ σ ]ᵥ)
  `let K `in G [ σ ]ₖ = `let (K [ σ ]ₖ) `in {!!}
  (match V `with K) [ σ ]ₖ = match V [ σ ]ᵥ `with {!!}
  opₖ op p V K [ σ ]ₖ = opₖ op p (V [ σ ]ᵥ) {!!}
  getenv K [ σ ]ₖ = getenv {!!}
  setenv x K [ σ ]ₖ = {!!}
  user M `with K [ σ ]ₖ = user (M [ σ ]ᵤ) `with {!!}
