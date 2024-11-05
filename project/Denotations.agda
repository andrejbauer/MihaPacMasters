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


-- A computation tree that hold values of type T in their leaves
data Tree (T : Set) : Set where
  leaf : T → Tree T
  node : ∀ (op : Op) → ⟦ param op ⟧g → (⟦ result op ⟧g → Tree T) → Tree T
  error : Tree T

-- Denotation of a user computation returning elements of X
U : Set → Set
U X = Tree X

-- Denotation of a kernel computation with state C returning elements of X
K : Set → Set → Set
K C X = C → Tree (X × C)

mutual
  -- Denotation of value types
  ⟦_⟧v : VType → Set

  ⟦ gnd g ⟧v = ⟦ g ⟧g
  ⟦ t ×v u ⟧v = ⟦ t ⟧v × ⟦ u ⟧v
  ⟦ t ⟶ᵤ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧u
  ⟦ t ⟶ₖ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧k
  ⟦ Σ₁ ⇒ Σ₂ , c ⟧v = Runner ⟦ c ⟧g

  -- Denotation of a skeletal runner
  Runner : Set → Set
  Runner C = ∀ (op : Op) → ⟦ param op ⟧g → K C ⟦ result op ⟧g

  -- Denotation of user computation types
  -- Idea: the elements of t!Σ are computations, each computation
  -- either returns a value of type t, or triggers an operation in Σ
  -- This is described by a *computation tree*:
  -- * leaves: return value
  -- * tree node: labeled by an operation and a parameter,
  --              subtrees are computations
  ⟦_⟧u : UType → Set
  ⟦ t ! _ ⟧u = U ⟦ t ⟧v

  -- Denotation of kernel computation types
  ⟦_⟧k : KType → Set
  ⟦ t ↯ _ , c ⟧k = K ⟦ c ⟧g ⟦ t ⟧v

-- Denotation of contexts are runtime environments
⟦_⟧-ctx : Ctx → Set
⟦ [] ⟧-ctx = ⊤
⟦ Γ ∷ t ⟧-ctx = ⟦ Γ ⟧-ctx × ⟦ t ⟧v

-- Lookup a variable in a runtime environment
lookup : ∀ {Γ t} (x : t ∈ Γ) → ⟦ Γ ⟧-ctx → ⟦ t ⟧v
lookup here η = proj₂ η
lookup (there x) η = lookup x (proj₁ η)

mutual
  -- Denotation of value subtyping
  coerceᵥ : ∀ {t u} → t ⊑ᵥ u → ⟦ t ⟧v → ⟦ u ⟧v
  coerceᵥ ⊑ᵥ-ground a = a
  coerceᵥ (⊑ᵥ-product p q) (a₁ , a₂) = (coerceᵥ p a₁ , coerceᵥ q a₂)
  coerceᵥ (⊑ᵥ-Ufun p q) f = λ a' →  coerceᵤ q (f (coerceᵥ p a'))
  coerceᵥ (⊑ᵥ-Kfun p q) f = {!!}
  coerceᵥ (⊑ᵥ-runner p q eq) a = λ op z z₁ → node op z (λ z₂ → leaf (z₂ , z₁))

  -- Denotation of user computation subtyping
  coerceᵤ : ∀ {t u} → t ⊑ᵤ u → ⟦ t ⟧u → ⟦ u ⟧u
  coerceᵤ p a = {!!}

  -- Denotation of user computation subtyping
  coerceₖ : ∀ {t u} → t ⊑ₖ u → ⟦ t ⟧k → ⟦ u ⟧k
  coerceₖ p a = {!!}


-- Denotations of terms
mutual

  ⟦_⟧-value : ∀ {Γ t} → (Γ ⊢V: t) → ⟦ Γ ⟧-ctx → ⟦ t ⟧v
  ⟦ var x ⟧-value η = lookup x η
  ⟦ sub-value t p ⟧-value η = coerceᵥ p (⟦ t ⟧-value η)
  ⟦ ⟨⟩ ⟧-value η = tt
  ⟦ ⟨ V , W ⟩ ⟧-value η = (⟦ V ⟧-value η) , (⟦ W ⟧-value η)
  ⟦ funM t ⟧-value η = λ a → ⟦ t ⟧-user (η , a)
  ⟦ funK t ⟧-value η = {!   !}
  ⟦ runner r ⟧-value η = λ op a c → {! !}

  ⟦_⟧-user : ∀ {Γ U} → (Γ ⊢U: U) → ⟦ Γ ⟧-ctx → ⟦ U ⟧u
  ⟦ sub-user M p ⟧-user η = {!   !}
  ⟦ return V ⟧-user η = leaf (⟦ V ⟧-value η)
  ⟦ V ∘ W ⟧-user η = ⟦ V ⟧-value η (⟦ W ⟧-value η)
  ⟦ opᵤ op p V M ⟧-user η = node op {!!} {!!}
  ⟦ `let M `in N ⟧-user η = {!   !}
  ⟦ match V `with M ⟧-user η = {!   !}
  ⟦ `using V at W `run M finally N ⟧-user η = {!   !}
  ⟦ kernel K at V finally M ⟧-user η = {!   !}

  ⟦_⟧-kernel : ∀ {Γ K} → (Γ ⊢K: K) → ⟦ Γ ⟧-ctx → ⟦ K ⟧k
  ⟦ sub-kernel K p ⟧-kernel η = {!   !}
  ⟦ return V ⟧-kernel η c = {!   !}
  ⟦ V ∘ W ⟧-kernel η = {!   !}
  ⟦ `let K `in L ⟧-kernel η c = {!   !}
  ⟦ match V `with K ⟧-kernel η = {!   !}
  ⟦ opₖ op p V K ⟧-kernel η c = {!   !}
  ⟦ getenv K ⟧-kernel η c = ⟦ K ⟧-kernel (η , c) c
  ⟦ setenv V K ⟧-kernel η _ = ⟦ K ⟧-kernel η (⟦ V ⟧-value η)
  ⟦ user M `with K ⟧-kernel η c = {!   !}
