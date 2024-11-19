{-# OPTIONS --allow-unsolved-metas #-}

open import Parameters

module Renaming (G : GTypes) (O : Ops G) where

open import Types G O
open import Terms G O
open import Contexts G O

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

extendᵣ : ∀ {Γ Γ' X Y} → Ren Γ' Γ → (X ∈ (Γ ∷ Y)) → (X ∈ (Γ' ∷ Y))
extendᵣ ρ here = here
extendᵣ ρ (there x) = there (ρ x)

extdᵣ : ∀ {Γ Γ' X} → Ren Γ' Γ → Ren (Γ' ∷ X) (Γ ∷ X)
extdᵣ ρ here = here
extdᵣ ρ (there p) = there (ρ p)



-- Action of renamings

interleaved mutual



  _[_]ᵥᵣ : ∀{Γ Γ' X} → Γ' ⊢V: X → Ren Γ Γ' → Γ ⊢V: X
  _[_]ᵤᵣ : ∀{Γ Γ' X} → Γ' ⊢U: X → Ren Γ Γ' → Γ ⊢U: X
  _[_]ₖᵣ : ∀{Γ Γ' X} → Γ' ⊢K: X → Ren Γ Γ' → Γ ⊢K: X

  rename-funK : ∀ {Γ Γ' X Y } → Γ ⊢V: X ⟶ₖ Y → Ren Γ' Γ → Γ' ⊢V: X ⟶ₖ Y  -- EXPLANATION: TODO
  rename-funK (var x) ρ = var (ρ x)
  rename-funK (sub-value V p) ρ = sub-value (V [ ρ ]ᵥᵣ) p
  rename-funK (funK K) ρ = funK (K [ extendᵣ ρ ]ₖᵣ)

  -- Value
  -- Explanation: This auxilliary function is used to use renamings within the co-op construct
  rename-coop : ∀ { Γ Γ' Σ C op} → co-op Γ Σ C op → Ren Γ' Γ → co-op Γ' Σ C op -- This might be doable in a less brute force way
  rename-coop (sub-kernel K p) ρ = sub-kernel (K [ extendᵣ ρ ]ₖᵣ) p
  rename-coop (return V) ρ = return (V [ extendᵣ ρ ]ᵥᵣ)
  rename-coop (V · U) ρ = rename-funK V (extendᵣ ρ) · (U [ extendᵣ ρ ]ᵥᵣ)
  rename-coop (`let K `in L) ρ = `let K [ extendᵣ ρ ]ₖᵣ `in (L [ extendᵣ (extendᵣ ρ) ]ₖᵣ)
  rename-coop (match V `with K) ρ = match V [ extendᵣ ρ ]ᵥᵣ `with (K [ extendᵣ (extendᵣ (extendᵣ ρ)) ]ₖᵣ)
  rename-coop (opₖ op p V K) ρ = opₖ op p (V [ extendᵣ ρ ]ᵥᵣ) (K [ extendᵣ (extendᵣ ρ) ]ₖᵣ)
  rename-coop (getenv K) ρ = getenv (K [ extendᵣ (extendᵣ ρ) ]ₖᵣ)
  rename-coop (setenv V K) ρ = setenv (V [ extendᵣ ρ ]ᵥᵣ) (K [ extendᵣ ρ ]ₖᵣ)
  rename-coop (user M `with K) ρ = user M [ extendᵣ ρ ]ᵤᵣ `with (K [ extendᵣ (extendᵣ ρ) ]ₖᵣ)

  rename-runner : ∀ { Γ Γ' Σ Σ' C} → ((op : Op) → op ∈ₒ Σ → co-op Γ Σ' C op) → Ren Γ' Γ → ((op : Op) → op ∈ₒ Σ → co-op Γ' Σ' C op)
  rename-runner R ρ op p = rename-coop (R op p) ρ

  var x [ ρ ]ᵥᵣ = var (ρ x)
  sub-value V x [ ρ ]ᵥᵣ = sub-value ( V [ ρ ]ᵥᵣ) x
  ⟨⟩ [ ρ ]ᵥᵣ = ⟨⟩
  ⟨ V , W ⟩ [ ρ ]ᵥᵣ = ⟨  V [ ρ ]ᵥᵣ , W [ ρ ]ᵥᵣ ⟩
  (funU M) [ ρ ]ᵥᵣ = funU (M [ extendᵣ ρ ]ᵤᵣ) -- EXPLANATION: We know that ρ won't change the funU constructor, so we can simply use the action of ρ on M
                                           -- with the addition of an extra variable as a function adds that
  (funK K) [ ρ ]ᵥᵣ = funK (K [ extendᵣ ρ ]ₖᵣ)
  runner R [ ρ ]ᵥᵣ = runner (rename-runner R ρ)

  -- User
  sub-user M x [ ρ ]ᵤᵣ = sub-user (M [ ρ ]ᵤᵣ) x
  return V [ ρ ]ᵤᵣ = return (V [ ρ ]ᵥᵣ)
  (V₁ · V₂) [ ρ ]ᵤᵣ = (V₁ [ ρ ]ᵥᵣ) · (V₂ [ ρ ]ᵥᵣ)
  opᵤ op p V M [ ρ ]ᵤᵣ = opᵤ op p (V [ ρ ]ᵥᵣ) (M [ extendᵣ ρ ]ᵤᵣ)
  `let M `in N [ ρ ]ᵤᵣ = `let M [ ρ ]ᵤᵣ `in (N [ extendᵣ ρ ]ᵤᵣ )
  (match M `with N) [ ρ ]ᵤᵣ = match M [ ρ ]ᵥᵣ `with (N [ extendᵣ (extendᵣ ρ) ]ᵤᵣ)
  `using M at N `run K finally L [ ρ ]ᵤᵣ = `using M [ ρ ]ᵥᵣ at N [ ρ ]ᵥᵣ `run K [ ρ ]ᵤᵣ finally (L [ extendᵣ (extendᵣ ρ) ]ᵤᵣ)
  kernel K at M finally N [ ρ ]ᵤᵣ = kernel K [ ρ ]ₖᵣ at M [ ρ ]ᵥᵣ finally (N [ extendᵣ (extendᵣ ρ) ]ᵤᵣ)

  -- Kernel
  sub-kernel K p [ ρ ]ₖᵣ = sub-kernel (K [ ρ ]ₖᵣ) p
  return V [ ρ ]ₖᵣ = return (V [ ρ ]ᵥᵣ)
  (V · U) [ ρ ]ₖᵣ = rename-funK V ρ · (U [ ρ ]ᵥᵣ) -- rename-funK necessary here, because I do not know how to prove anything about Γ ⊢V: X ⟶ₖ Y
  `let K `in L [ ρ ]ₖᵣ = `let K [ ρ ]ₖᵣ `in (L [ extendᵣ ρ ]ₖᵣ)
  match V `with K [ ρ ]ₖᵣ = match V [ ρ ]ᵥᵣ `with (K [ extendᵣ (extendᵣ ρ) ]ₖᵣ)
  opₖ op p V K [ ρ ]ₖᵣ = opₖ op p (V [ ρ ]ᵥᵣ) (K [ extendᵣ ρ ]ₖᵣ)
  getenv K [ ρ ]ₖᵣ = getenv (K [ extendᵣ ρ ]ₖᵣ)
  setenv V K [ ρ ]ₖᵣ = setenv (V [ ρ ]ᵥᵣ) (K [ ρ ]ₖᵣ)
  user U `with K [ ρ ]ₖᵣ = user U [ ρ ]ᵤᵣ `with (K [ extendᵣ ρ ]ₖᵣ)
 