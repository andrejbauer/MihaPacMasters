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
  coerceᵥ (⊑ᵥ-runner p q refl) r = λ op p' param C → include-tree q (r op (p _ p') param C) -- TODO: Make the first argument of p implicit 

  -- Denotation of user computation subtyping
  coerceᵤ : ∀ {X Y} → X ⊑ᵤ Y → ⟦ X ⟧u → ⟦ Y ⟧u
  coerceᵤ (⊑ᵤ-user p q) M = include-tree q (map-tree (coerceᵥ p) M)

  -- Denotation of kernel computation subtyping
  coerceₖ : ∀ {Xₖ Yₖ} → Xₖ ⊑ₖ Yₖ → ⟦ Xₖ ⟧k → ⟦ Yₖ ⟧k
  coerceₖ (⊑ₖ-kernel p q refl) K C = include-tree q (map-tree (λ {(X , C') → (coerceᵥ p X) , C'}) (K C))


--aux3 : ∀ {Γ C Σ Σ' X} → (V : Γ ⊢V: gnd C) → (R : Γ ⊢V: (Σ ⇒ Σ' , C)) → (M : Γ ⊢U: X ! Σ) → (M' : Γ ⊢U: X ! Σ')
--aux3 = ?

aux3 : ∀ {Γ C Σ Σ' X} → Γ ⊢V: gnd C → Γ ⊢V: (Σ ⇒ Σ' , C) → Γ ⊢U: (X ! Σ) → Γ ⊢U: X ! Σ'
aux3 C R M = {!   !}

-- Denotations of terms
mutual

--  sub-coop : ∀ { } → 

  ⟦_⟧-value : ∀ {Γ X} → (Γ ⊢V: X) → ⟦ Γ ⟧-ctx → ⟦ X ⟧v
  ⟦ var p ⟧-value η = lookup p η
  ⟦ sub-value v p ⟧-value η = coerceᵥ p (⟦ v ⟧-value η)
  ⟦ ⟨⟩ ⟧-value η = tt
  ⟦ ⟨ v , w ⟩ ⟧-value η = (⟦ v ⟧-value η) , (⟦ w ⟧-value η)
  ⟦ funU m ⟧-value η = λ X → ⟦ m ⟧-user (η , X)
  ⟦ funK k ⟧-value η = λ X → ⟦ k ⟧-kernel (η , X)
  ⟦ runner r ⟧-value η = λ op p param → ⟦ (r op p) ⟧-kernel (η , param) --Removed C from the ends of this

{-   using-runner : ∀ { Γ X Σ Σ' C} → UComp Σ X → Runner Σ Σ' C → UComp Σ' X --TODO (7. 1. 2025): THINK IF THIS ACTUALLY IS WHAT YOU NEED
  using-runner (leaf X) R = leaf X
  using-runner (node op p param t) R = node op {!   !} param (λ res → {! R op p param  !})

  bind-runner-user : ∀ {Σ Σ' C X Y} → ⟦ C ⟧g → Runner Σ Σ' ⟦ C ⟧g → UComp Σ X → UComp Σ' Y
  bind-runner-user C R (Monads.leaf x) = {! R ? ? ? ?  !}
  bind-runner-user C R (Monads.node op p param₁ t) = {!   !} -}

  aux2 : ∀ {Σ' result C X } → Tree Σ' (⟦ result ⟧g × ⟦ C ⟧g) → (⟦ result ⟧g × ⟦ C ⟧g → ⟦ X ⟧v) → Tree Σ' ⟦ X ⟧v
  aux2 {Σ'} R f = bind-tree (λ x → {! Tree Σ' (f x)  !}) R

  wrap-runner : ∀ {Γ Σ Σ' C X} → ⟦ Γ ⟧-ctx → Γ ⊢V: (Σ ⇒ Σ' , C) → Γ ⊢V: gnd C → Γ ⊢U: (X ! Σ) → UComp Σ' ⟦ X ⟧v
  wrap-runner η r c (sub-user m p) = {!   !}
  wrap-runner η r c (return x) = leaf (⟦ x ⟧-value η)
  wrap-runner η r c (x · x₁) = {!   !}
  wrap-runner η r c (opᵤ op p par m) = bind-tree (λ x → {!   !}) (⟦ r ⟧-value η op p (⟦ par ⟧-value η) (⟦ c ⟧-value η))
  wrap-runner η r c (`let m `in m₁) = {!   !}
  wrap-runner η r c (match x `with m) = {!   !}
  wrap-runner η r c (`using r' at c' `run m finally n) = wrap-runner η {!   !} {!   !} {!   !}
  wrap-runner η r c (kernel x at x₁ finally m) = {!   !}

  ⟦_⟧-user : ∀ {Γ Xᵤ} → (Γ ⊢U: Xᵤ) → ⟦ Γ ⟧-ctx → ⟦ Xᵤ ⟧u
  ⟦ sub-user m p ⟧-user η = coerceᵤ p (⟦ m ⟧-user η)
  ⟦ return v ⟧-user η = leaf (⟦ v ⟧-value η)
  ⟦ v · w ⟧-user η = ⟦ v ⟧-value η (⟦ w ⟧-value η)
  ⟦ opᵤ op p v m ⟧-user η = node op p (⟦ v ⟧-value η) λ res → ⟦ m ⟧-user (η , res)
  ⟦ `let m `in n ⟧-user η = bind-user (λ X → ⟦ n ⟧-user (η , X)) (⟦ m ⟧-user η)
  ⟦ match v `with m ⟧-user η = ⟦ m ⟧-user ((η , (proj₁ (⟦ v ⟧-value η))) , (proj₂ (⟦ v ⟧-value η)))
  ⟦ `using r at c `run m finally n ⟧-user η = bind-tree (λ x → ⟦ n ⟧-user ((η , {!   !}) , ⟦ c ⟧-value η)) {!   !}
    --bind-tree (λ {x → ⟦ n ⟧-user ((η , x) , ⟦ c ⟧-value η)} ) (wrap-runner η r c m) 
  ⟦ kernel k at c finally m ⟧-user η = bind-user (λ {(X , C) → ⟦ m ⟧-user ((η , X) , C)} ) (⟦ k ⟧-kernel η (⟦ c ⟧-value η))

  ⟦_⟧-kernel : ∀ {Γ K} → (Γ ⊢K: K) → ⟦ Γ ⟧-ctx → ⟦ K ⟧k
  ⟦ sub-kernel k p ⟧-kernel η = coerceₖ p (⟦ k ⟧-kernel η)
  ⟦ return v ⟧-kernel η C = leaf ((⟦ v ⟧-value η) , C)
  ⟦ v · w ⟧-kernel η = ⟦ v ⟧-value η (⟦ w ⟧-value η)
  ⟦ `let k `in l ⟧-kernel η = bind-kernel (λ X → ⟦ l ⟧-kernel (η , X)) (⟦ k ⟧-kernel η)
  ⟦ match v `with k ⟧-kernel η = ⟦ k ⟧-kernel ((η , proj₁ (⟦ v ⟧-value η)) , proj₂ (⟦ v ⟧-value η))
  ⟦ opₖ op p v k ⟧-kernel η C =  node op p (⟦ v ⟧-value η) (λ res → ⟦ k ⟧-kernel (η , res) C)
  ⟦ getenv k ⟧-kernel η C = ⟦ k ⟧-kernel (η , C) C
  ⟦ setenv v k ⟧-kernel η _ = ⟦ k ⟧-kernel η (⟦ v ⟧-value η)
  ⟦ user m `with k ⟧-kernel η C = bind-tree (λ { X → ⟦ k ⟧-kernel (η , X) C}) (⟦ m ⟧-user η)
  --⟦ K ⟧-kernel (η , {! ⟦ ? ⟧-user  !}) C
   


--TODOs for next time (17. 12. 2024)
--1. Split Denotations.agda into 2 files, one file has all definitions regarding Monads, the other has the ⟦ ⟧ stuff, except the ⟦ ⟧g stuff (which goes with Monads). DONE
--2. Use consistent fixed variable names. Then keep it consistent forevermore. DONE
--3. Finish the definitions of the ⟦ ⟧-kernel and ⟦ ⟧-user 
--- ^What is expected^ --
--3.5. Rewrite the ⟦ ⟧ stuff to use the Monad structure
--4. getenv, setenv and the equations they use (for the Kernel Monad), algebraic operations, algebraicity equation (for both monads)
--Optional: Read the literature already given. Most important is that the Runners paper is understood as much as possible, the rest is simply background reading to understand that.
--Keep track of things you do not understand. Danel's thesis will be useful for HOW to write your own thesis. The MFPS2013 paper will also be useful.          