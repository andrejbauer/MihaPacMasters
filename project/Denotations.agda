{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
--open import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function

import Contexts
open import Parameters
import Types
import Terms
import Monads

module Denotations (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O
open Monads G O 

-- GENERAL TODO: naming conventions (think for yourself what to do, try to stay close to the paper/thesis)
-- - upper-case letters for types, lower-case letters for terms
-- - use X, Y, Z for value types
-- - use A, B, C for ground types
-- - something for base types? (could be 'b')
-- - use Xᵤ, Yᵤ, Zᵤ for user types
-- - use Xₖ, Yₖ, Zₖ  for kernel types

-- Trees are t, u, ...
-- UComps are M, N, ... 
-- KComps are K, L, ...
-- Values are V, W, ...

-- TODO: look up "Wadler's law" (named after Phil Wadler)

mutual --TODO: This should go into a different module/file. Essentially putting the monads in one and the ⟦ ⟧ stuff into another file.
  -- Denotation of value types
  ⟦_⟧v : VType → Set

  ⟦ gnd A ⟧v = ⟦ A ⟧g
  ⟦ X ×v Y ⟧v = ⟦ X ⟧v × ⟦ Y ⟧v
  ⟦ X ⟶ᵤ Y ⟧v = ⟦ X ⟧v → ⟦ Y ⟧u
  ⟦ X ⟶ₖ Y ⟧v = ⟦ X ⟧v → ⟦ Y ⟧k
  ⟦ Σ₁ ⇒ Σ₂ , C ⟧v = Runner Σ₁ Σ₂ ⟦ C ⟧g

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
  ⟦ X ! Σ ⟧u = UComp Σ ⟦ X ⟧v

  -- Denotation of kernel computation types
  ⟦_⟧k : KType → Set
  ⟦ X ↯ Σ , C ⟧k = KComp Σ ⟦ C ⟧g ⟦ X ⟧v

-- Denotation of contexts are runtime environments
⟦_⟧-ctx : Ctx → Set
⟦ [] ⟧-ctx = ⊤
⟦ Γ ∷ X ⟧-ctx = ⟦ Γ ⟧-ctx × ⟦ X ⟧v

-- Lookup a variable in a runtime environment
lookup : ∀ {Γ t} (x : t ∈ Γ) → ⟦ Γ ⟧-ctx → ⟦ t ⟧v
lookup here η = proj₂ η
lookup (there p) η = lookup p (proj₁ η)

mutual
  -- Denotation of value subtyping
  coerceᵥ : ∀ {t u} → t ⊑ᵥ u → ⟦ t ⟧v → ⟦ u ⟧v
  coerceᵥ ⊑ᵥ-ground A = A
  coerceᵥ (⊑ᵥ-product p q) (X , Y) = (coerceᵥ p X , coerceᵥ q Y)
  coerceᵥ (⊑ᵥ-Ufun p q) f = λ X' → coerceᵤ q (f (coerceᵥ p X'))
  coerceᵥ (⊑ᵥ-Kfun p q) f = λ X' → coerceₖ q (f (coerceᵥ p X'))
  coerceᵥ (⊑ᵥ-runner p q refl) r = λ op p' param state → include-tree q (r op (p _ p') param state) -- TODO: Make the first argument of p implicit 

  -- Denotation of user computation subtyping
  coerceᵤ : ∀ {X Y} → X ⊑ᵤ Y → ⟦ X ⟧u → ⟦ Y ⟧u
  coerceᵤ (⊑ᵤ-user p q) M = include-tree q (map-tree (coerceᵥ p) M)

  -- Denotation of kernel computation subtyping
  coerceₖ : ∀ {Xₖ Yₖ} → Xₖ ⊑ₖ Yₖ → ⟦ Xₖ ⟧k → ⟦ Yₖ ⟧k
  coerceₖ (⊑ₖ-kernel p q refl) K C = include-tree q (map-tree (λ {(X , C') → (coerceᵥ p X) , C'}) (K C))


-- Denotations of terms
mutual

--  sub-coop : ∀ { } → 

  ⟦_⟧-value : ∀ {Γ X} → (Γ ⊢V: X) → ⟦ Γ ⟧-ctx → ⟦ X ⟧v
  ⟦ var p ⟧-value η = lookup p η
  ⟦ sub-value v p ⟧-value η = coerceᵥ p (⟦ v ⟧-value η)
  ⟦ ⟨⟩ ⟧-value η = tt
  ⟦ ⟨ V , W ⟩ ⟧-value η = (⟦ V ⟧-value η) , (⟦ W ⟧-value η)
  ⟦ funU M ⟧-value η = λ a → ⟦ M ⟧-user (η , a)
  ⟦ funK K ⟧-value η = λ a → ⟦ K ⟧-kernel (η , a)
  ⟦ runner r ⟧-value η = λ op p param C → ⟦ (r op p) ⟧-kernel (η , param) C

  ⟦_⟧-user : ∀ {Γ U} → (Γ ⊢U: U) → ⟦ Γ ⟧-ctx → ⟦ U ⟧u
  ⟦ sub-user M p ⟧-user η = coerceᵤ p (⟦ M ⟧-user η)
  ⟦ return V ⟧-user η = leaf (⟦ V ⟧-value η)
  ⟦ V · W ⟧-user η = ⟦ V ⟧-value η (⟦ W ⟧-value η)
  ⟦ opᵤ op p V M ⟧-user η = node op p (⟦ V ⟧-value η) λ res → ⟦ M ⟧-user (η , res)
  ⟦ `let M `in N ⟧-user η = bind-user (λ X → ⟦ N ⟧-user (η , X)) (⟦ M ⟧-user η)
  ⟦ match V `with M ⟧-user η = ⟦ M ⟧-user ((η , (proj₁ (⟦ V ⟧-value η))) , (proj₂ (⟦ V ⟧-value η)))
  ⟦ `using R at V `run M finally N ⟧-user η = {!   !} --{! ⟦ R ⟧-value η !}
  ⟦ kernel K at V finally M ⟧-user η = {!   !} --bind-user (λ (x , y) → ⟦ M ⟧-user ((η , x) , y)) (bind-kernel (λ x' c' → ⟦ K ⟧-kernel η c') {!   !} {!   !})

  ⟦_⟧-kernel : ∀ {Γ K} → (Γ ⊢K: K) → ⟦ Γ ⟧-ctx → ⟦ K ⟧k
  ⟦ sub-kernel K p ⟧-kernel η = coerceₖ p (⟦ K ⟧-kernel η)
  ⟦ return V ⟧-kernel η C = leaf ((⟦ V ⟧-value η) , C)
  ⟦ V · W ⟧-kernel η = ⟦ V ⟧-value η (⟦ W ⟧-value η)
  ⟦ `let K `in L ⟧-kernel η = bind-kernel (λ X → ⟦ L ⟧-kernel (η , X)) (⟦ K ⟧-kernel η)
  ⟦ match V `with K ⟧-kernel η = ⟦ K ⟧-kernel ((η , proj₁ (⟦ V ⟧-value η)) , proj₂ (⟦ V ⟧-value η))
  ⟦ opₖ op p V K ⟧-kernel η C =  node op p (⟦ V ⟧-value η) (λ res → ⟦ K ⟧-kernel (η , res) C)
  ⟦ getenv K ⟧-kernel η C = ⟦ K ⟧-kernel (η , C) C
  ⟦ setenv V K ⟧-kernel η _ = ⟦ K ⟧-kernel η (⟦ V ⟧-value η)
  ⟦ user M `with K ⟧-kernel η C = {!   !}
   


--TODOs for next time (17. 12. 2024)
--1. Split Denotations.agda into 2 files, one file has all definitions regarding Monads, the other has the ⟦ ⟧ stuff, except the ⟦ ⟧g stuff (which goes with Monads). DONE
--2. Use consistent fixed variable names. Then keep it consistent forevermore. DONE
--3. Finish the definitions of the ⟦ ⟧-kernel and ⟦ ⟧-user 
--- ^What is expected^ --
--3.5. Rewrite the ⟦ ⟧ stuff to use the Monad structure
--4. getenv, setenv and the equations they use (for the Kernel Monad), algebraic operations, algebraicity equation (for both monads)
--Optional: Read the literature already given. Most important is that the Runners paper is understood as much as possible, the rest is simply background reading to understand that.
--Keep track of things you do not understand. Danel's thesis will be useful for HOW to write your own thesis. The MFPS2013 paper will also be useful.  