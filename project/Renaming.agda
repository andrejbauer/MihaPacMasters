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

-- add one element renaming 
addᵣ : ∀ {Γ X} → Ren (Γ ∷ X) Γ
addᵣ here = there here
addᵣ (there x) = there (there x)

-- auxilliary function that helps with proving the ∈ relation when functions are involved
-- as it does nothing to the variable the function adds
-- "nof" for "Not (the) first (element)"

nofᵣ : ∀ {Γ Γ' X Y} → Ren Γ' Γ → (X ∈ (Γ ∷ Y)) → (X ∈ (Γ' ∷ Y))
nofᵣ ρ here = here
nofᵣ ρ (there x) = there (ρ x)




-- Action of renamings

interleaved mutual



  _[_]ᵥᵣ : ∀{Γ Γ' X} → Γ' ⊢V: X → Ren Γ Γ' → Γ ⊢V: X
  _[_]ᵤᵣ : ∀{Γ Γ' X} → Γ' ⊢M: X → Ren Γ Γ' → Γ ⊢M: X
  _[_]ₖᵣ : ∀{Γ Γ' X} → Γ' ⊢K: X → Ren Γ Γ' → Γ ⊢K: X

  -- THE FOLLOWING IS AN AUXILLIARY FUNCTION
  -- Something for Γ ⊢V: X ⟶ₖ Y and ρ = Ren Γ' Γ FOR (V ∘ U) (Named nth for nothing)
  -- Explanation: It takes a value calculation(Not right term) of a specific type and a renaming, then
  -- proves that the renaming transforms the calculation(?) in the expected way  
  nthᵣ : ∀ {Γ Γ' X Y } → Γ ⊢V: X ⟶ₖ Y → Ren Γ' Γ → Γ' ⊢V: X ⟶ₖ Y  -- EXPLANATION: TODO
  nthᵣ (var x) ρ = var (ρ x)
  nthᵣ (sub-value V p) ρ = sub-value (V [ ρ ]ᵥᵣ) p
  nthᵣ (funK K) ρ = funK (K [ nofᵣ ρ ]ₖᵣ)
  
  -- Value
  -- THE FOLLOWING IS AN AUXILLIARY FUNCTION
  -- MIGHT BE SUPERFLUOUS (might exist a better method)
  -- Explanation: This auxilliary function is used to use renamings within the co-op construct
  runn : ∀ { Γ Γ' Σ C op} → co-op Γ Σ C op → Ren Γ' Γ → co-op Γ' Σ C op -- This might be doable in a less brute force way
  runn (sub-kernel K p) ρ = sub-kernel (K [ nofᵣ ρ ]ₖᵣ) p
  runn (return V) ρ = return (V [ nofᵣ ρ ]ᵥᵣ)
  runn (V ∘ U) ρ = nthᵣ V (nofᵣ ρ) ∘ (U [ nofᵣ ρ ]ᵥᵣ)
  runn (`let K `in L) ρ = `let K [ nofᵣ ρ ]ₖᵣ `in (L [ nofᵣ (nofᵣ ρ) ]ₖᵣ)
  runn (match V `with K) ρ = match V [ nofᵣ ρ ]ᵥᵣ `with (K [ nofᵣ (nofᵣ (nofᵣ ρ)) ]ₖᵣ)
  runn (opₖ op p V K) ρ = opₖ op p (V [ nofᵣ ρ ]ᵥᵣ) (K [ nofᵣ (nofᵣ ρ) ]ₖᵣ)
  runn (getenv K) ρ = getenv (K [ nofᵣ (nofᵣ ρ) ]ₖᵣ)
  runn (setenv V K) ρ = setenv (V [ nofᵣ ρ ]ᵥᵣ) (K [ nofᵣ ρ ]ₖᵣ)
  runn (user M `with K) ρ = user M [ nofᵣ ρ ]ᵤᵣ `with (K [ nofᵣ (nofᵣ ρ) ]ₖᵣ)

  -- A similar thing for runners specifically THIS MIGHT BE SUPERFLUOUS (might exist a better method)

  runᵣ : ∀ { Γ Γ' Σ Σ' C op } → ((op : Op) → op ∈ₒ Σ → co-op Γ Σ' C op) → Ren Γ' Γ → ((op : Op) → op ∈ₒ Σ → co-op Γ' Σ' C op)
  runᵣ R ρ op p = runn (R op p) ρ

  var x [ ρ ]ᵥᵣ = var (ρ x)
  sub-value V x [ ρ ]ᵥᵣ = sub-value ( V [ ρ ]ᵥᵣ) x
  ⟨⟩ [ ρ ]ᵥᵣ = ⟨⟩
  ⟨ V , W ⟩ [ ρ ]ᵥᵣ = ⟨  V [ ρ ]ᵥᵣ , W [ ρ ]ᵥᵣ ⟩
  (funM M) [ ρ ]ᵥᵣ = funM (M [ nofᵣ ρ ]ᵤᵣ) -- EXPLANATION: We know that ρ won't change the funM constructor, so we can simply use the action of ρ on M
                                           -- with the addition of an extra variable as a function adds that
  (funK K) [ ρ ]ᵥᵣ = funK (K [ nofᵣ ρ ]ₖᵣ) -- EXPLANATION: This method is repeated throughout
  runner R [ ρ ]ᵥᵣ = runner {!   !} -- runner (runᵣ R ρ) -- EXPLANATION: I am unsure if this even works
  -- User
  sub-user M x [ ρ ]ᵤᵣ = sub-user (M [ ρ ]ᵤᵣ) x
  return V [ ρ ]ᵤᵣ = return (V [ ρ ]ᵥᵣ)
  (V₁ ∘ V₂) [ ρ ]ᵤᵣ = (V₁ [ ρ ]ᵥᵣ) ∘ (V₂ [ ρ ]ᵥᵣ)
  opᵤ op p V M [ ρ ]ᵤᵣ = opᵤ op p (V [ ρ ]ᵥᵣ) (M [ nofᵣ ρ ]ᵤᵣ)
  `let M `in N [ ρ ]ᵤᵣ = `let M [ ρ ]ᵤᵣ `in (N [ nofᵣ ρ ]ᵤᵣ ) -- Explanation: standard method
  (match M `with N) [ ρ ]ᵤᵣ = match M [ ρ ]ᵥᵣ `with (N [ nofᵣ (nofᵣ ρ) ]ᵤᵣ) -- EXPLANATION: standard method
  `using M at N `run K finally L [ ρ ]ᵤᵣ = `using M [ ρ ]ᵥᵣ at N [ ρ ]ᵥᵣ `run K [ ρ ]ᵤᵣ finally (L [ nofᵣ (nofᵣ ρ) ]ᵤᵣ) -- EXPLANATION: standard method
  kernel K at M finally N [ ρ ]ᵤᵣ = kernel K [ ρ ]ₖᵣ at M [ ρ ]ᵥᵣ finally (N [ nofᵣ (nofᵣ ρ) ]ᵤᵣ)
  -- Kernel -- EXPLANATIONS: The standard method throughout
  sub-kernel K p [ ρ ]ₖᵣ = sub-kernel (K [ ρ ]ₖᵣ) p
  return V [ ρ ]ₖᵣ = return (V [ ρ ]ᵥᵣ)
  (V ∘ U) [ ρ ]ₖᵣ = nthᵣ V ρ ∘ (U [ ρ ]ᵥᵣ) -- nthᵣ necessary here, because I do not know how to prove anything about Γ ⊢V: X ⟶ₖ Y
  `let K `in L [ ρ ]ₖᵣ = `let K [ ρ ]ₖᵣ `in (L [ nofᵣ ρ ]ₖᵣ)
  match V `with K [ ρ ]ₖᵣ = match V [ ρ ]ᵥᵣ `with (K [ nofᵣ (nofᵣ ρ) ]ₖᵣ)
  opₖ op p V K [ ρ ]ₖᵣ = opₖ op p (V [ ρ ]ᵥᵣ) (K [ nofᵣ ρ ]ₖᵣ)
  getenv K [ ρ ]ₖᵣ = getenv (K [ nofᵣ ρ ]ₖᵣ)
  setenv V K [ ρ ]ₖᵣ = setenv (V [ ρ ]ᵥᵣ) (K [ ρ ]ₖᵣ)
  user U `with K [ ρ ]ₖᵣ = user U [ ρ ]ᵤᵣ `with (K [ nofᵣ ρ ]ₖᵣ)
 
-- ...
    