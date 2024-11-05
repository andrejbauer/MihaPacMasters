open import Data.Unit
open import Data.Product

import Contexts
open import Parameters
import Types
import Terms

module Denotations (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O

-- Denotation of ground types
⟦_⟧g : GType → Set
⟦ base b ⟧g =  ⟦ b ⟧b
⟦ unit ⟧g = ⊤
⟦ g ×b h ⟧g = ⟦ g ⟧g × ⟦ h ⟧g


-- (Skeletal) user computation trees that hold values of type T in their leaves
data UTree (T : Set) : Set where
  leafᵘ : T → UTree T
  nodeᵘ : ∀ (op : Op) → ⟦ param op ⟧g → (⟦ result op ⟧g → UTree T) → UTree T

data KTree (T : Set) : Set where
  leafᵏ : T → KTree T
  nodeᵏ : ∀ (op : Op) → {!   !} → ( {!   !} ) → KTree T

mutual
  -- Denotation of value types
  ⟦_⟧v : VType → Set

  ⟦ gnd g ⟧v = ⟦ g ⟧g
  ⟦ t ×v u ⟧v = ⟦ t ⟧v × ⟦ u ⟧v --????
  ⟦ t ⟶ᵤ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧u
  ⟦ t ⟶ₖ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧k
  ⟦ Σ₁ ⇒ Σ₂ , C ⟧v = Runner Σ₁ Σ₂ C

  -- Denotation of a runner
  Runner : ∀ (Σ₁ : Sig) (Σ₂ : Sig) (C : KState) → Set
  Runner Σ₁ Σ₂ C = {! C !}

  -- Denotation of user computation types
  -- Idea: the elements of t!Σ are computations, each computation
  -- either returns a value of type t, or triggers an operation in Σ
  -- This is described by a *computation tree*:
  -- * leaves: return value
  -- * tree node: labeled by an operation and a parameter,
  --              subtrees are computations
  ⟦_⟧u : UType → Set
  ⟦ t ! _ ⟧u = UTree ⟦ t ⟧v


  -- Denotation of kernel computation types
  ⟦_⟧k : KType → Set
  ⟦ t ↯ _ , _ ⟧k = KTree ⟦ t ⟧v

-- Denotation of contexts
⟦_⟧-ctx : Ctx → Set
⟦ [] ⟧-ctx = ⊤
⟦ Γ ∷ t ⟧-ctx = ⟦ Γ ⟧-ctx × ⟦ t ⟧v

-- Denotations of terms
⟦_⟧-value : ∀ {Γ t} → (Γ ⊢V: t) → ⟦ Γ ⟧-ctx → ⟦ t ⟧v
⟦ var x ⟧-value Γ = {!   !}
⟦ sub-value x p ⟧-value Γ = {!   !}
⟦ ⟨⟩ ⟧-value Γ = tt
⟦ ⟨ V , W ⟩ ⟧-value Γ = {!   !} , {!   !}
⟦ funM x ⟧-value Γ = {!   !}
⟦ funK x ⟧-value Γ = {!   !}
⟦ runner x ⟧-value Γ = {!   !}
  
⟦_⟧-user : ∀ {Γ t Σ} → (Γ ⊢U: t ! Σ) → ⟦ Γ ⟧-ctx → ⟦ t ! Σ ⟧u
⟦ sub-user M p ⟧-user Γ = {!   !}
⟦ return V ⟧-user Γ = {!   !}
⟦ V ∘ W ⟧-user Γ = {!   !}
⟦ opᵤ op p V M ⟧-user Γ = {!   !}
⟦ `let M `in N ⟧-user Γ = {!   !}
⟦ match V `with M ⟧-user Γ = {!   !}
⟦ `using V at W `run M finally N ⟧-user Γ = {!   !}
⟦ kernel K at V finally M ⟧-user Γ = {!   !}

⟦_⟧-kernel : ∀ {Γ t Σ C} → (Γ ⊢K: t ↯ Σ , C) → ⟦ Γ ⟧-ctx → ⟦ t ↯ Σ , C ⟧k
⟦ sub-kernel K p ⟧-kernel Γ = {!   !}
⟦ return V ⟧-kernel Γ = {!   !}
⟦ V ∘ W ⟧-kernel Γ = {!   !}
⟦ `let K `in L ⟧-kernel Γ = {!   !}
⟦ match V `with K ⟧-kernel Γ = {!   !}
⟦ opₖ op p V K ⟧-kernel Γ = {!   !}
⟦ getenv K ⟧-kernel Γ = {!   !}
⟦ setenv V K ⟧-kernel Γ = {!   !}
⟦ user M `with K ⟧-kernel Γ = {!   !} 