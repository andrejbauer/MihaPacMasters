open import Parameters

module Substitution (G : GTypes) (O : Ops G) where

open import Types G O
open import Terms G O
open import Contexts G O
open import Renaming G O

open GTypes G
open Ops O

-- Type of substitutions

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ' → Γ ⊢V: X

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ = var

-- Auxiliary functions for substitutions

-- note: we probably should generalize this so that the extra variable (of type `X`)
--       maps to a given term, not necessarily itself
-- TASK: implement this one as two simpler functions:
--       (1) σ : Sub Γ Γ' is transformed to σ' : Sub (Γ ∷ X) Γ'
--       (2) given τ : Sub Δ Δ' and Δ ⊢ v : X, we get ⟨τ, v⟩ : Sub Δ (Δ' ∷ X)

extendₛ : ∀ {Γ Γ' X} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
extendₛ σ here = var here
extendₛ σ (there p) =  σ p [ wkᵣ ]ᵥᵣ

wkₛ : ∀ {Γ Γ' X} → Sub Γ Γ' → Sub (Γ ∷ X) Γ'
wkₛ σ p = σ p [ wkᵣ ]ᵥᵣ
--wkₛ σ here = σ here [ wkᵣ ]ᵥᵣ -- To add another variable to the start, we have to simply say that we will add a new variable at the start
--wkₛ σ (there p) =  σ (obvious p) [ wkᵣ ]ᵥᵣ -- EXPLAIN WHAT wkᵣ ACTUALLY DOES

_∷ₛ_ : ∀ {Γ Γ' X} → Sub Γ Γ' → Γ ⊢V: X → Sub Γ (Γ' ∷ X)
(σ ∷ₛ V) here = V
(σ ∷ₛ V) (there p) = σ p


-- Action of substitutions

interleaved mutual

  _[_]ᵥ : ∀{Γ Γ' X} → Γ' ⊢V: X → Sub Γ Γ' → Γ ⊢V: X
  _[_]ᵤ : ∀{Γ Γ' X} → Γ' ⊢U: X → Sub Γ Γ' → Γ ⊢U: X
  _[_]ₖ : ∀{Γ Γ' X} → Γ' ⊢K: X → Sub Γ Γ' → Γ ⊢K: X

  sub-coop : ∀ {Γ Γ' Σ C op} → co-op Γ Σ C op → Sub Γ' Γ → co-op Γ' Σ C op
  sub-coop (sub-kernel K p) σ = sub-kernel (K [ (extendₛ σ) ]ₖ) p
  sub-coop (return V) σ = return (V [ (extendₛ σ) ]ᵥ)
  sub-coop (V · U) σ = (V [ extendₛ σ ]ᵥ) · (U [ (extendₛ σ) ]ᵥ)
  sub-coop (`let K `in L) σ = `let K [ (extendₛ σ) ]ₖ `in (L [ (extendₛ (extendₛ σ)) ]ₖ)
  sub-coop (match V `with K) σ = match (V [ extendₛ σ ]ᵥ) `with (K [ (extendₛ (extendₛ (extendₛ σ))) ]ₖ)
  sub-coop (opₖ op p V K) σ = opₖ op p (V [ (extendₛ σ) ]ᵥ) (K [ (extendₛ (extendₛ σ)) ]ₖ)
  sub-coop (getenv K) σ = getenv (K [ (extendₛ (extendₛ σ)) ]ₖ)
  sub-coop (setenv V K) σ = setenv (V [ (extendₛ σ) ]ᵥ) (K [ (extendₛ σ) ]ₖ)
  sub-coop (user M `with K) σ = user (M [ (extendₛ σ) ]ᵤ) `with (K [ (extendₛ (extendₛ σ)) ]ₖ)

  var p [ σ ]ᵥ = σ p
  sub-value V p [ σ ]ᵥ = sub-value (V [ σ ]ᵥ) p
  ⟨⟩ [ σ ]ᵥ = ⟨⟩
  ⟨ V , W ⟩ [ σ ]ᵥ = ⟨ V [ σ ]ᵥ , W [ σ ]ᵥ ⟩
  (funU M) [ σ ]ᵥ = funU ( M [ extendₛ σ ]ᵤ)
  (funK K) [ σ ]ᵥ = funK (K [ extendₛ σ ]ₖ)
  runner R [ σ ]ᵥ = runner λ op p → sub-coop (R op p) σ

  sub-user M x [ σ ]ᵤ = sub-user (M [ σ ]ᵤ) x
  return V [ σ ]ᵤ = return (V [ σ ]ᵥ)
  (V₁ ∘ V₂) [ σ ]ᵤ = (V₁ [ σ ]ᵥ) ∘ (V₂ [ σ ]ᵥ)
  opᵤ op p V M [ σ ]ᵤ = opᵤ op p (V [ σ ]ᵥ) (M [ extendₛ σ ]ᵤ)
  `let M `in N [ σ ]ᵤ = `let M [ σ ]ᵤ `in (N [ (extendₛ σ) ]ᵤ)
  (match V `with M) [ σ ]ᵤ = match (V [ σ ]ᵥ) `with (M [ (extendₛ (extendₛ σ)) ]ᵤ)
  `using V at U `run M finally N [ σ ]ᵤ = `using V [ σ ]ᵥ at U [ σ ]ᵥ `run M [ σ ]ᵤ finally (N [ extendₛ (extendₛ σ) ]ᵤ)
  kernel K at V finally M [ σ ]ᵤ = kernel (K [ σ ]ₖ) at (V [ σ ]ᵥ) finally (M [ (extendₛ (extendₛ σ)) ]ᵤ)

  sub-kernel K p [ σ ]ₖ = sub-kernel (K [ σ ]ₖ) p
  return V [ σ ]ₖ = return (V [ σ ]ᵥ)
  (V₁ · V₂) [ σ ]ₖ = (V₁ [ σ ]ᵥ) · (V₂ [ σ ]ᵥ)
  `let K `in L [ σ ]ₖ = `let (K [ σ ]ₖ) `in (L [ (extendₛ σ) ]ₖ)
  (match V `with K) [ σ ]ₖ = match V [ σ ]ᵥ `with (K [ (extendₛ (extendₛ σ)) ]ₖ)
  opₖ op p V K [ σ ]ₖ = opₖ op p (V [ σ ]ᵥ) (K [ extendₛ σ ]ₖ)
  getenv K [ σ ]ₖ = getenv (K [ (extendₛ σ) ]ₖ)
  setenv V K [ σ ]ₖ = setenv (V [ σ ]ᵥ) (K [ σ ]ₖ)
  user M `with K [ σ ]ₖ = user (M [ σ ]ᵤ) `with (K [ (extendₛ σ) ]ₖ)
