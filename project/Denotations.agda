open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

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

-- GENERAL TODO: naming conventions (think for yourself what to do, try to stay close to the paper/thesis)
-- - upper-case letters for types, lower-case letters for terms
-- - use X, Y, Z for value types
-- - use A, B, C for ground types
-- - something for base types? (could be 'b')
-- - use Xᵤ, Yᵤ, Zᵤ for user types
-- - use Xk, Yk, Zk  for kernel types

-- TODO: look up "Wadler's law" (named after Phil Wadler)

-- Denotation of ground types
⟦_⟧g : GType → Set
⟦ base b ⟧g =  ⟦ b ⟧b
⟦ unit ⟧g = ⊤
⟦ A ×b B ⟧g = ⟦ A ⟧g × ⟦ B ⟧g


-- A computation tree that hold values of type T in their leaves
data Tree  (Σ : Sig) (X : Set) : Set where
  leaf : X → Tree Σ X
  node : ∀ (op : Op) → op ∈ₒ Σ → ⟦ param op ⟧g → (⟦ result op ⟧g → Tree Σ X) → Tree Σ X

include-tree : ∀ {Σ₁ Σ₂ X} → Σ₁ ⊆ₛ Σ₂ → Tree Σ₁ X → Tree Σ₂ X
include-tree p t = {!!} -- TODO

-- Monadic bind for trees
bind-tree : ∀ {Σ X Y} → (X → Tree Σ Y) → Tree Σ X → Tree Σ Y
bind-tree f (leaf x) = f x
bind-tree f (node op p par c) = node op p par (λ res → bind-tree f (c res))

map-tree : ∀ {Σ X Y} → (X → Y) → Tree Σ X → Tree Σ Y
map-tree f t = bind-tree (leaf ∘ f) t

-- Denotation of a user computation returning elements of X and performing operations Σ
UComp : Sig → Set → Set
UComp Σ X = Tree Σ X

-- TODO: write the type of bind-user
bind-user = bind-tree

-- Denotation of a kernel computation with state C returning elements of X
KComp : Sig → Set → Set → Set
KComp Σ C X = C → Tree Σ (X × C)

bind-kernel : ∀ {Σ C X Y} → (X → KComp Σ C Y) → (KComp Σ C X → KComp Σ C Y)
bind-kernel = {!!} -- TODO

mutual
  -- Denotation of value types
  ⟦_⟧v : VType → Set

  ⟦ gnd g ⟧v = ⟦ g ⟧g
  ⟦ t ×v u ⟧v = ⟦ t ⟧v × ⟦ u ⟧v
  ⟦ t ⟶ᵤ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧u
  ⟦ t ⟶ₖ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧k
  ⟦ Σ₁ ⇒ Σ₂ , c ⟧v = Runner Σ₁ Σ₂ ⟦ c ⟧g

  -- Denotation of a skeletal runner
  Runner : Sig → Sig → Set → Set
  Runner Σ₁ Σ₂ C = ∀ (op : Op) → op ∈ₒ Σ₁ → ⟦ param op ⟧g → KComp Σ₂ C ⟦ result op ⟧g

  -- Denotation of user computation types
  -- Idea: the elements of t!Σ are computations, each computation
  -- either returns a value of type t, or triggers an operation in Σ
  -- This is described by a *computation tree*:
  -- * leaves: return value
  -- * tree node: labeled by an operation and a parameter,
  --              subtrees are computations
  ⟦_⟧u : UType → Set
  ⟦ t ! Σ ⟧u = UComp Σ ⟦ t ⟧v

  -- Denotation of kernel computation types
  ⟦_⟧k : KType → Set
  ⟦ t ↯ Σ , c ⟧k = KComp Σ ⟦ c ⟧g ⟦ t ⟧v

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
  coerceᵥ (⊑ᵥ-Ufun p q) f = λ a' → coerceᵤ q (f (coerceᵥ p a'))
  coerceᵥ (⊑ᵥ-Kfun p q) f = λ a' → coerceₖ q (f (coerceᵥ p a'))
  coerceᵥ (⊑ᵥ-runner p q refl) R = λ op r par state → include-tree q (R op {!!} par state)

  -- Denotation of user computation subtyping
  coerceᵤ : ∀ {X Y} → X ⊑ᵤ Y → ⟦ X ⟧u → ⟦ Y ⟧u
  coerceᵤ (⊑ᵤ-ground p q) t = {!!} -- TODO: use include-tree and map-tree on t

  -- Denotation of kernel computation subtyping
  coerceₖ : ∀ {t u} → t ⊑ₖ u → ⟦ t ⟧k → ⟦ u ⟧k
  coerceₖ (⊑ₖ-kernel val sig refl) a = λ c' → {!!} -- TODO: like above


-- Denotations of terms
mutual

  ⟦_⟧-value : ∀ {Γ t} → (Γ ⊢V: t) → ⟦ Γ ⟧-ctx → ⟦ t ⟧v
  ⟦ var x ⟧-value η = lookup x η
  ⟦ sub-value t p ⟧-value η = coerceᵥ p (⟦ t ⟧-value η)
  ⟦ ⟨⟩ ⟧-value η = tt
  ⟦ ⟨ V , W ⟩ ⟧-value η = (⟦ V ⟧-value η) , (⟦ W ⟧-value η)
  ⟦ funU t ⟧-value η = λ a → ⟦ t ⟧-user (η , a)
  ⟦ funK t ⟧-value η = λ a → ⟦ t ⟧-kernel (η , a)
  ⟦ runner r ⟧-value η = {!!}

  ⟦_⟧-user : ∀ {Γ U} → (Γ ⊢U: U) → ⟦ Γ ⟧-ctx → ⟦ U ⟧u
  ⟦ sub-user M p ⟧-user η = coerceᵤ p (⟦ M ⟧-user η)
  ⟦ return V ⟧-user η = leaf (⟦ V ⟧-value η)
  ⟦ V · W ⟧-user η = ⟦ V ⟧-value η (⟦ W ⟧-value η)
  ⟦ opᵤ op p V M ⟧-user η = node op p (⟦ V ⟧-value η) λ res → ⟦ M ⟧-user (η , res)
  ⟦ `let M `in N ⟧-user η = ⟦ N ⟧-user (η , {!  !}) -- TODO: use bind-user here
  ⟦ match V `with M ⟧-user η = ⟦ M ⟧-user ((η , (proj₁ (⟦ V ⟧-value η))) , (proj₂ (⟦ V ⟧-value η)))
  ⟦ `using V at W `run M finally N ⟧-user η = {!   !}
  ⟦ kernel K at V finally M ⟧-user η = {!  ⟦ K ⟧-kernel η   !}

  ⟦_⟧-kernel : ∀ {Γ K} → (Γ ⊢K: K) → ⟦ Γ ⟧-ctx → ⟦ K ⟧k
  ⟦ sub-kernel K p ⟧-kernel η = coerceₖ p (⟦ K ⟧-kernel η)
  ⟦ return V ⟧-kernel η c = leaf ((⟦ V ⟧-value η) , c)
  ⟦ V · W ⟧-kernel η = ⟦ V ⟧-value η (⟦ W ⟧-value η)
  ⟦ `let K `in L ⟧-kernel η c = {!   !} -- TODO: use bind-kernel here
  ⟦ match V `with K ⟧-kernel η = ⟦ K ⟧-kernel ((η , proj₁ (⟦ V ⟧-value η)) , proj₂ (⟦ V ⟧-value η))
  ⟦ opₖ op p V K ⟧-kernel η c =  node op p (⟦ V ⟧-value η) (λ res → ⟦ K ⟧-kernel (η , res) c)
  ⟦ getenv K ⟧-kernel η c = ⟦ K ⟧-kernel (η , c) c
  ⟦ setenv V K ⟧-kernel η _ = ⟦ K ⟧-kernel η (⟦ V ⟧-value η)
  ⟦ user M `with K ⟧-kernel η c = {!   !}
