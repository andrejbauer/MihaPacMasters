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
(σ ∷ₛ v) here = v
(σ ∷ₛ v) (there p) = σ p


-- Action of substitutions

interleaved mutual

  _[_]ᵥ : ∀{Γ Γ' X} → Γ' ⊢V: X → Sub Γ Γ' → Γ ⊢V: X
  _[_]ᵤ : ∀{Γ Γ' X} → Γ' ⊢U: X → Sub Γ Γ' → Γ ⊢U: X
  _[_]ₖ : ∀{Γ Γ' X} → Γ' ⊢K: X → Sub Γ Γ' → Γ ⊢K: X

  sub-coop : ∀ {Γ Γ' Σ C op} → co-op Γ Σ C op → Sub Γ' Γ → co-op Γ' Σ C op
  sub-coop (sub-kernel k p) σ = sub-kernel (k [ (extendₛ σ) ]ₖ) p
  sub-coop (return v) σ = return (v [ (extendₛ σ) ]ᵥ)
  sub-coop (v · u) σ = (v [ extendₛ σ ]ᵥ) · (u [ (extendₛ σ) ]ᵥ)
  sub-coop (`let k `in l) σ = `let k [ (extendₛ σ) ]ₖ `in (l [ (extendₛ (extendₛ σ)) ]ₖ)
  sub-coop (match v `with k) σ = match (v [ extendₛ σ ]ᵥ) `with (k [ (extendₛ (extendₛ (extendₛ σ))) ]ₖ)
  sub-coop (opₖ op p v k) σ = opₖ op p (v [ (extendₛ σ) ]ᵥ) (k [ (extendₛ (extendₛ σ)) ]ₖ)
  sub-coop (getenv k) σ = getenv (k [ (extendₛ (extendₛ σ)) ]ₖ)
  sub-coop (setenv v k) σ = setenv (v [ (extendₛ σ) ]ᵥ) (k [ (extendₛ σ) ]ₖ)
  sub-coop (user m `with k) σ = user (m [ (extendₛ σ) ]ᵤ) `with (k [ (extendₛ (extendₛ σ)) ]ₖ)

  -- Value
  var p [ σ ]ᵥ = σ p
  sub-value v p [ σ ]ᵥ = sub-value (v [ σ ]ᵥ) p
  ⟨⟩ [ σ ]ᵥ = ⟨⟩
  ⟨ v , w ⟩ [ σ ]ᵥ = ⟨ v [ σ ]ᵥ , w [ σ ]ᵥ ⟩
  (funU m) [ σ ]ᵥ = funU (m [ extendₛ σ ]ᵤ)
  (funK k) [ σ ]ᵥ = funK (k [ extendₛ σ ]ₖ)
  runner r [ σ ]ᵥ = runner λ op p → sub-coop (r op p) σ

  -- User
  sub-user m p [ σ ]ᵤ = sub-user (m [ σ ]ᵤ) p
  return v [ σ ]ᵤ = return (v [ σ ]ᵥ)
  (v₁ · v₂) [ σ ]ᵤ = (v₁ [ σ ]ᵥ) · (v₂ [ σ ]ᵥ)
  opᵤ op p v m [ σ ]ᵤ = opᵤ op p (v [ σ ]ᵥ) (m [ extendₛ σ ]ᵤ)
  `let m `in n [ σ ]ᵤ = `let m [ σ ]ᵤ `in (n [ (extendₛ σ) ]ᵤ)
  (match v `with m) [ σ ]ᵤ = match (v [ σ ]ᵥ) `with (m [ (extendₛ (extendₛ σ)) ]ᵤ)
  `using v at w `run m finally n [ σ ]ᵤ = `using v [ σ ]ᵥ at w [ σ ]ᵥ `run m [ σ ]ᵤ finally (n [ extendₛ (extendₛ σ) ]ᵤ)
  kernel k at v finally m [ σ ]ᵤ = kernel (k [ σ ]ₖ) at (v [ σ ]ᵥ) finally (m [ (extendₛ (extendₛ σ)) ]ᵤ)

  -- Kernel
  sub-kernel k p [ σ ]ₖ = sub-kernel (k [ σ ]ₖ) p
  return v [ σ ]ₖ = return (v [ σ ]ᵥ)
  (v₁ · v₂) [ σ ]ₖ = (v₁ [ σ ]ᵥ) · (v₂ [ σ ]ᵥ)
  `let k `in l [ σ ]ₖ = `let (k [ σ ]ₖ) `in (l [ (extendₛ σ) ]ₖ)
  (match v `with k) [ σ ]ₖ = match v [ σ ]ᵥ `with (k [ (extendₛ (extendₛ σ)) ]ₖ)
  opₖ op p v k [ σ ]ₖ = opₖ op p (v [ σ ]ᵥ) (k [ extendₛ σ ]ₖ)
  getenv k [ σ ]ₖ = getenv (k [ (extendₛ σ) ]ₖ)
  setenv v k [ σ ]ₖ = setenv (v [ σ ]ᵥ) (k [ σ ]ₖ)
  user m `with k [ σ ]ₖ = user (m [ σ ]ᵤ) `with (k [ (extendₛ σ) ]ₖ)
