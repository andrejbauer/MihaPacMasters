--{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning     -- using ( _≡⟨⟩_ ; _∎ ; begin_) renaming (begin_ to start_ ; step-≡ to step-= ) 
--(begin_ to start_ ; _≡⟨⟩_ to _=<>_ ; step-≡ to step-= ; _∎ to _qed) 
-- using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function

import Contexts
open import Parameters
import Types
import Terms
import Monads
import Equations
import Denotations

module Sub-Validity (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O
open Monads G O
open Equations G O
open Denotations G O 
open import Renaming G O 
open import Substitution G O

{-Tezave:
Kako delati karkoli z "extend sigma"-}

mutual
-- Naming scheme for the various equalities:
--   Γ ⊢V v ≡ w will be named eq-v, eq-w, ...
--   Γ ⊢U m ≡ n will be named eq-m, eq-n, ...
--   Γ ⊢K k ≡ l will be named eq-k, eq-l, ...
-- This naming scheme will be to quickly show the type of equivalence.

    ⟦_⟧-sub : ∀ {Γ Γ'} → Sub Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx  
    ⟦_⟧-sub {Γ' = []} σ η = tt
    ⟦_⟧-sub {Γ' = Γ' ∷ X} σ η = (⟦ σ ∘ there ⟧-sub η) , ⟦ σ here ⟧-value η

    ⟦_⟧-ren : ∀ {Γ Γ'} → Ren Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx
    ⟦_⟧-ren {Γ' = []} ρ η = tt
    ⟦_⟧-ren {Γ' = Γ' ∷ X} ρ η = ⟦ ρ ∘ there ⟧-ren η , lookup (ρ here) η


    to-sub : ∀ {Γ Γ'} 
        → Ren Γ Γ' → Sub Γ Γ'
    to-sub ρ x = var (ρ x) 

    sub-to-ren : ∀ {Γ Γ'} → (ρ : Ren Γ Γ') → (η : ⟦ Γ ⟧-ctx) 
        → ⟦ to-sub ρ ⟧-sub η ≡ ⟦ ρ ⟧-ren η
    sub-to-ren {Γ} {[]} ρ η = refl
    sub-to-ren {Γ} {Γ' ∷ X} ρ η = cong₂ _,_ (sub-to-ren (ρ ∘ there) η) refl

    ren-env : ∀ {Γ Γ' X} {ρ : Ren Γ Γ'} {η : ⟦ Γ ⟧-ctx} → (x : X ∈ Γ') 
        → lookup x (⟦ ρ ⟧-ren η) ≡ lookup (ρ x) η
    ren-env {Γ} {Γ'} {X} {ρ} {η} here = refl
    ren-env {Γ} {Γ'} {X} {ρ} {η} (there x) = ren-env {ρ = ρ ∘ there} x

    lookup-ext : ∀ {Γ} {η η' : ⟦ Γ ⟧-ctx} → (∀ {X} (x : X ∈ Γ) 
        → lookup x η ≡ lookup x η') → η ≡ η'
    lookup-ext {[]} {η} {η'} eq = refl
    lookup-ext {Γ ∷ X} {η , v} {η' , v'} eq = cong₂ _,_ (lookup-ext (eq ∘ there))  (eq here)
    --Maybe a lemma for cong₂ _,_ or maybe it's in the standard library

    sub-var : ∀ { Γ } {η : ⟦ Γ ⟧-ctx} 
        → η ≡ ⟦ var ⟧-sub η
    sub-var {Γ} {η} = Eq.trans (lookup-ext (λ x → Eq.sym (ren-env {ρ = idᵣ} x))) (Eq.sym (sub-to-ren idᵣ η))

    --sub-ren?
    --sub-ren-V
    --sub-ren-U
    --sub-ren-K
    sub-ren : ∀ { Γ Γ' Γ'' } (ρ : Ren Γ Γ') (σ : Sub Γ' Γ'')  (η : ⟦ Γ ⟧-ctx) --(η' : ⟦ Γ ⟧-ctx)
        → ⟦ σ ⟧-sub (⟦ ρ ⟧-ren η) ≡ ⟦ ρ ᵣ∘ₛ σ ⟧-sub η
        -- ⟦ σ ⟧-sub η ≡ ⟦ σ' ⟧-sub (η , x)
    sub-ren {Γ} {Γ'} {Contexts.[]} ρ σ η = refl
    sub-ren {Γ} {Γ'} {Γ'' Contexts.∷ x} ρ σ η = cong₂ _,_ 
        (sub-ren ρ ((λ x₁ → σ (there x₁))) η)
        (sub-ren-value (σ here) ρ η) 
        
    --sub-ren-value
    --sub-ren-user
    --sub-ren-kernel
    sub-ren-value : ∀ { Γ Γ' X} (V : Γ' ⊢V: X) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ V ⟧-value (⟦ ρ ⟧-ren η) ≡ ⟦ V [ ρ ]ᵥᵣ ⟧-value η
    sub-ren-value {Γ} {Γ'} (var x) ρ η = lookup-ren x ρ η
    sub-ren-value {Γ} {Γ'} (sub-value V x) ρ η = cong (coerceᵥ x) (sub-ren-value V ρ η) 
    sub-ren-value {Γ} {Γ'} ⟨⟩ ρ η = refl
    sub-ren-value {Γ} {Γ'} ⟨ V , W ⟩ ρ η = cong₂ _,_ (sub-ren-value V ρ η) (sub-ren-value W ρ η) 
    sub-ren-value {Γ} {Γ'} (funU x) ρ η = fun-ext (λ X 
        → cong₂ (λ a b → a b) {x =  ⟦ funU x ⟧-value (⟦ ρ ⟧-ren η)} {y = ⟦ funU x [ ρ ]ᵥᵣ ⟧-value η} 
            (fun-ext (λ Y → 
                Eq.trans 
                    (cong ⟦ x ⟧-user (cong₂ _,_ 
                        (ren-wk {v = Y} ρ η)
                        refl))
                    (sub-ren-user x (extendᵣ ρ) (η , Y))))  
            refl)
    sub-ren-value {Γ} {Γ'} (funK x) ρ η = fun-ext (λ X → 
        Eq.trans 
            (cong ⟦ x ⟧-kernel (cong₂ _,_ 
                (ren-wk {v = X} ρ η)
                refl)) 
            (sub-ren-kernel x (extendᵣ ρ) (η , X)))
    sub-ren-value {Γ} {Γ'} (runner x) ρ η = fun-ext (λ op → fun-ext (λ x' → fun-ext (λ param → 
        begin 
        ⟦ x op x' ⟧-kernel (⟦ ρ ⟧-ren η , param) 
        ≡⟨ {!   !} ⟩ 
        ⟦ x op x' ⟧-kernel (⟦ extendᵣ ρ ⟧-ren (η , param)) 
        ≡⟨ (sub-ren-kernel (x op x') (extendᵣ ρ) (η , param)) ⟩ 
        ⟦ x op x' [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , param) 
        ≡⟨ cong₂ (λ a b → a b) 
                {x = ⟦ x op x' [ extendᵣ ρ ]ₖᵣ ⟧-kernel}
                {y = ⟦ rename-coop (x op x') ρ ⟧-kernel}
                {u = η , param}
                {v = η , param}
                (cong ⟦_⟧-kernel 
                    {x = x op x' [ extendᵣ ρ ]ₖᵣ} 
                    {y = rename-coop (x op x') ρ} 
                    (little-lemma ρ (x op x')))
                refl ⟩ 
        refl)))

    little-lemma : ∀ { Γ Γ' Σ C op} (ρ : Ren Γ Γ') (coop : co-op Γ' Σ C op)
        → coop [ extendᵣ ρ ]ₖᵣ ≡ rename-coop coop ρ
    little-lemma ρ (sub-kernel coop x) = refl
    little-lemma ρ (return x) = refl
    little-lemma ρ (x · x₁) = refl
    little-lemma ρ (`let coop `in coop₁) = refl
    little-lemma ρ (match x `with coop) = refl
    little-lemma ρ (opₖ op₁ x x₁ coop) = refl
    little-lemma ρ (getenv coop) = refl
    little-lemma ρ (setenv x coop) = refl
    little-lemma ρ (user x `with coop) = refl

{-(λ op x₁ param₁ → ⟦ x op x₁ ⟧-kernel (⟦ ρ ⟧-ren η , param₁))
      ≡
      (λ op x₁ param₁ → ⟦ rename-coop (x op x₁) ρ ⟧-kernel (η , param₁))-}
    sub-ren-user : ∀ { Γ Γ' Xᵤ} (M : Γ' ⊢U: Xᵤ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ M ⟧-user (⟦ ρ ⟧-ren η) ≡ ⟦ M [ ρ ]ᵤᵣ ⟧-user η
    sub-ren-user {Γ} {Γ'} {Xᵤ} (sub-user M p) ρ η = cong (coerceᵤ p) (sub-ren-user M ρ η) 
    sub-ren-user {Γ} {Γ'} {Xᵤ} (return V) ρ η = cong leaf (sub-ren-value V ρ η)
    sub-ren-user {Γ} {Γ'} {Xᵤ} (V · W) ρ η = cong₂ (λ a b → a b) (sub-ren-value V ρ η) (sub-ren-value W ρ η) 
    sub-ren-user {Γ} {Γ'} {Xᵤ} (opᵤ op x par M) ρ η = cong₂ (node op x) 
        (sub-ren-value par ρ η) 
        (fun-ext (λ res → Eq.trans 
                (cong ⟦ M ⟧-user (cong₂ _,_
                    (ren-wk {v = res} ρ η)
                    refl))
                (sub-ren-user M (extendᵣ ρ) (η , res)))) 
    sub-ren-user {Γ} {Γ'} {Xᵤ} (`let M `in N) ρ η = cong₂ bind-tree 
        (fun-ext (λ X → Eq.trans
            (cong ⟦ N ⟧-user (cong₂ _,_
                (ren-wk {v = X} ρ η)
                refl))
            (sub-ren-user N (extendᵣ ρ) (η , X)))) 
        (sub-ren-user M ρ η)
    sub-ren-user {Γ} {Γ'} {Xᵤ} (match V `with M) ρ η = 
        begin 
        (⟦ M ⟧-user ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) , proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η)))
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ 
            {y = {! η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)  !}}
            {v = proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)} 
            (cong₂ _,_ 
                refl
                (cong proj₁ (sub-ren-value V ρ η)))
            (cong proj₂ (sub-ren-value V ρ η))) ⟩
        ⟦ M ⟧-user
          ((⟦ ρ ⟧-ren η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) ,
           proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ 
            (cong₂ _,_ 
                (Eq.trans 
                    (ren-wk ρ η)
                    (ren-wk (ρ ∘ᵣ there) (η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))) 
                refl) 
            refl) ⟩
        ⟦ M ⟧-user (⟦ extendᵣ {X = {!   !}} (extendᵣ {X = {!   !}} ρ) ⟧-ren ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))
        ≡⟨ sub-ren-user M (extendᵣ (extendᵣ ρ)) ((η , (proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) , (proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) ⟩ 
        refl)
    sub-ren-user {Γ} {Γ'} {Xᵤ} (`using R at C `run M finally N) ρ η = cong₂ bind-tree
        {x = (λ { (x , c') → ⟦ N ⟧-user ((⟦ ρ ⟧-ren η , x) , c') })}
        {y = λ { (x , c') → ⟦ N [ extendᵣ (extendᵣ ρ) ]ᵤᵣ ⟧-user ((η , x) , c')}}
        {u = (apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C ⟧-value (⟦ ρ ⟧-ren η)))}
        {v = (apply-runner (⟦ R [ ρ ]ᵥᵣ ⟧-value η) (⟦ M [ ρ ]ᵤᵣ ⟧-user η) (⟦ C [ ρ ]ᵥᵣ ⟧-value η))}
        (fun-ext (λ {(x , c') → 
            begin 
                (⟦ N ⟧-user ((⟦ ρ ⟧-ren η , x) , c') 
                ≡⟨ cong ⟦ N ⟧-user (cong₂ _,_ 
                    (cong₂ _,_ 
                        (Eq.trans 
                            (ren-wk ρ η)
                            (ren-wk (ρ ∘ᵣ there) (η , x)))
                        refl) 
                    refl) ⟩ 
                ⟦ N ⟧-user (⟦ extendᵣ (extendᵣ {X = {!   !}} ρ) ⟧-ren ((η , x) , c')) --TODO 26. 3. : X = requires to be the type of x
                ≡⟨ sub-ren-user N (extendᵣ (extendᵣ ρ)) ((η , x) , c') ⟩ 
                refl)}))
{- ⟦ N ⟧-user ((⟦ ρ ⟧-ren η , x) , c')
≡ 
⟦ N [ extendᵣ (extendᵣ ρ) ]ᵤᵣ ⟧-user ((η , x) , c') -}
        (begin 
            apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C ⟧-value (⟦ ρ ⟧-ren η)) 
            ≡⟨ cong (apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η))) (sub-ren-value C ρ η) ⟩ 
            apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C [ ρ ]ᵥᵣ ⟧-value η) 
            ≡⟨ cong₂ (λ a b → apply-runner a b (⟦ C [ ρ ]ᵥᵣ ⟧-value η)) 
                {x = (⟦ R ⟧-value (⟦ ρ ⟧-ren η))}
                {y = (⟦ R [ ρ ]ᵥᵣ ⟧-value η)}
                {u = (⟦ M ⟧-user (⟦ ρ ⟧-ren η))}
                {v = (⟦ M [ ρ ]ᵤᵣ ⟧-user η)}
                (sub-ren-value R ρ η) 
                (sub-ren-user M ρ η) ⟩ 
            apply-runner (⟦ R [ ρ ]ᵥᵣ ⟧-value η) (⟦ M [ ρ ]ᵤᵣ ⟧-user η) (⟦ C [ ρ ]ᵥᵣ ⟧-value η) 
        ∎)

    sub-ren-user {Γ} {Γ'} {Xᵤ} (kernel K at C finally M) ρ η = cong₂ bind-tree 
        {x = (λ { (X , C) → ⟦ M ⟧-user ((⟦ ρ ⟧-ren η , X) , C) })}
        {y = (λ { (X , C) → ⟦ M [ extendᵣ (extendᵣ ρ) ]ᵤᵣ ⟧-user ((η , X) , C)})}
        {u = (⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) (⟦ C ⟧-value (⟦ ρ ⟧-ren η)))}
        {v = (⟦ K [ ρ ]ₖᵣ ⟧-kernel η (⟦ C [ ρ ]ᵥᵣ ⟧-value η))}
        (fun-ext (λ (X , C) → 
            begin
            ⟦ M ⟧-user ((⟦ ρ ⟧-ren η , X) , C) 
            ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ 
                (cong₂ _,_ 
                    (Eq.trans 
                        (ren-wk ρ η)
                        (ren-wk (ρ ∘ᵣ there) (η , X)))
                    refl) 
                refl) ⟩ 
            ⟦ M ⟧-user (⟦ extendᵣ (extendᵣ {X = {!   !}} ρ) ⟧-ren ((η , X) , C)) 
            ≡⟨ sub-ren-user M (extendᵣ (extendᵣ ρ)) ((η , X) , C) ⟩ 
            refl 
        ))
{- ⟦ M ⟧-user ((⟦ ρ ⟧-ren η , X) , C) ≡ ⟦ M [ extendᵣ (extendᵣ ρ) ]ᵤᵣ ⟧-user ((η , X) , C) -}
        (cong₂ (λ a b → a b) 
            (sub-ren-kernel K ρ η) 
            (sub-ren-value C ρ η)) 

    sub-ren-kernel : ∀ { Γ Γ' Xₖ} (K : Γ' ⊢K: Xₖ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) ≡ ⟦ K [ ρ ]ₖᵣ ⟧-kernel η
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (sub-kernel K p) ρ η = cong (coerceₖ p) (sub-ren-kernel K ρ η)
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (return V) ρ η = fun-ext (λ C → cong leaf (cong₂ _,_ (sub-ren-value V ρ η) refl))  
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (var x · W) ρ η = cong₂ (λ a b → a b) 
        {x = lookup x (⟦ ρ ⟧-ren η)}{y = lookup (ρ x) η} 
        {u = ⟦ W ⟧-value (⟦ ρ ⟧-ren η)}{v = ⟦ W [ ρ ]ᵥᵣ ⟧-value η} 
        (lookup-ren x ρ η) 
        (sub-ren-value W ρ η) 
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (sub-value V x · W) ρ η = cong₂ (λ a b → a b) 
        {x = coerceᵥ x (⟦ V ⟧-value (⟦ ρ ⟧-ren η))}{y = coerceᵥ x (⟦ V [ ρ ]ᵥᵣ ⟧-value η)}
        {u = ⟦ W ⟧-value (⟦ ρ ⟧-ren η)} {v = ⟦ W [ ρ ]ᵥᵣ ⟧-value η} 
        (cong (coerceᵥ x) (sub-ren-value V ρ η)) 
        (sub-ren-value W ρ η) 
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (funK K · W) ρ η = 
        begin 
        (⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , ⟦ W ⟧-value (⟦ ρ ⟧-ren η)) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_ 
            (ren-wk ρ η)
            (sub-ren-value W ρ η) ) ⟩ 
        ⟦ K ⟧-kernel (⟦ extendᵣ ρ ⟧-ren (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η))
        ≡⟨ refl ⟩ 
        ⟦ K ⟧-kernel (⟦ extendᵣ ρ ⟧-ren (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η)) 
        ≡⟨ sub-ren-kernel K (extendᵣ ρ) (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η) ⟩ 
        refl)
{-⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , ⟦ W ⟧-value (⟦ ρ ⟧-ren η)) ≡
      ⟦ K [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η)-}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (`let K `in L) ρ η = fun-ext (λ C → cong₂ bind-tree
        {x = (λ { (x , C') → ⟦ L ⟧-kernel (⟦ ρ ⟧-ren η , x) C' })}
        {y = (λ { (x , C') → ⟦ L [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , x) C' })}
        {u = (⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) C)}
        {v = (⟦ K [ ρ ]ₖᵣ ⟧-kernel η C)}
        (fun-ext (λ (x' , C') → 
           begin 
            ⟦ L ⟧-kernel (⟦ ρ ⟧-ren η , x') C' 
            ≡⟨ cong (λ a → ⟦ L ⟧-kernel a C') (cong₂ _,_ 
                (ren-wk ρ η) 
                refl) ⟩ 
            ⟦ L ⟧-kernel (⟦ extendᵣ ρ ⟧-ren (η , x')) C' 
            ≡⟨ cong₂ (λ a b → a b) 
                (sub-ren-kernel L (extendᵣ ρ) (η , x')) 
                refl ⟩ 
            (⟦ L [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , x') C') 
            ≡⟨ refl ⟩ 
            refl 
            ))
{- ⟦ L ⟧-kernel (⟦ ρ ⟧-ren η , x') C' ≡
      ⟦ L [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , x') C' -}
        (cong₂ (λ a b → a b) (sub-ren-kernel K ρ η) refl))
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (match V `with K) ρ η = 
        begin 
        (⟦ K ⟧-kernel ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) , proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_
            (cong₂ _,_ 
                refl 
                (cong proj₁ (sub-ren-value V ρ η)))
            (cong proj₂ (sub-ren-value V ρ η))) ⟩ 
        ⟦ K ⟧-kernel (((⟦ ρ ⟧-ren η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_ 
            (cong₂ _,_ 
                (Eq.trans
                    (ren-wk ρ η)
                    (ren-wk (ρ ∘ᵣ there) (η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))) 
                refl) 
            refl) ⟩
        ⟦ K ⟧-kernel (⟦ extendᵣ (extendᵣ ρ) ⟧-ren ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))  
        ≡⟨ sub-ren-kernel K (extendᵣ (extendᵣ ρ)) ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) ⟩ 
        ⟦ K [ extendᵣ (extendᵣ ρ) ]ₖᵣ ⟧-kernel ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) 
        ≡⟨ refl ⟩ 
        refl)
{- ⟦ K ⟧-kernel
      ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) ,
       proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η)))  ≡ 
    ⟦ K [ extendᵣ (extendᵣ ρ) ]ₖᵣ ⟧-kernel
      ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) ,
       proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) -}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (opₖ op x par K) ρ η = fun-ext (λ C → 
        cong₂ (node op x) 
            (sub-ren-value par ρ η) 
            (fun-ext (λ res → cong₂ (λ a b → a b)
                {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , res)}
                {y = ⟦ K [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , res)}
                (Eq.trans 
                    (cong ⟦ K ⟧-kernel (cong₂ _,_
                        (ren-wk ρ η)
                        refl)) 
                    (sub-ren-kernel K (extendᵣ ρ) (η , res))) 
                refl)))
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (getenv K) ρ η = fun-ext (λ C → 
        cong₂ (λ a b → a b) 
            {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , C)}
            {y = ⟦ K [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , C)}
            (Eq.trans 
                (cong ⟦ K ⟧-kernel (cong₂ _,_ 
                    (ren-wk ρ η)
                    refl))
                (sub-ren-kernel K (extendᵣ ρ) (η , C))) 
            refl)
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (setenv V K) ρ η = fun-ext (λ _ → 
        cong₂ (λ a b → a b) 
        {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η)}
        {y = ⟦ K [ ρ ]ₖᵣ ⟧-kernel η} 
        (sub-ren-kernel K ρ η) 
        (sub-ren-value V ρ η))
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (user M `with K) ρ η = fun-ext (λ C → 
        cong₂ bind-tree
            {u = (⟦ M ⟧-user (⟦ ρ ⟧-ren η))}
            {v = (⟦ M [ ρ ]ᵤᵣ ⟧-user η)}
            (fun-ext λ X' → cong₂ (λ a b → a b)
                {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , X')}
                {y = ⟦ K [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , X')}
                (Eq.trans
                    (cong ⟦ K ⟧-kernel (cong₂ _,_
                        (ren-wk ρ η)
                        refl))
                    (sub-ren-kernel K (extendᵣ ρ) (η , X')))
                refl)
            (sub-ren-user M ρ η))

    --lookup-ren
    lookup-ren : ∀ { Γ Γ' v} (x : v ∈ Γ') (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → lookup x (⟦ ρ ⟧-ren η) ≡ lookup (ρ x) η
    lookup-ren here ρ η = refl
    lookup-ren (there x) ρ η = lookup-ren x (λ x → ρ (there x)) η

    sub-wk : ∀ {Γ Γ' X} {v : ⟦ X ⟧v} (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ (λ y → there {Y = X} y) ]ᵥᵣ) ⟧-sub (η , v)
    sub-wk {Γ} {[]} σ η = refl
    sub-wk {Γ} {Γ' ∷ X'} {v = v} σ η = cong₂ _,_ 
        (sub-wk (σ ₛ∘ᵣ there) η)
        (begin 
        ⟦ σ here ⟧-value η 
        ≡⟨ cong ⟦ σ here ⟧-value (Eq.trans (sub-wk-lemma2 η) (ren-wk idᵣ η)) ⟩ 
        ⟦ σ here ⟧-value (⟦ there ⟧-ren (η , v))
        ≡⟨ sub-ren-value (σ here) there (η , _) ⟩ 
        refl)

    ren-wk : ∀ {Γ Γ' X} {v : ⟦ X ⟧v} (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx) 
        → ⟦ ρ ⟧-ren η ≡ ⟦ ρ ∘ᵣ there {Y = X} ⟧-ren (η , v)
    ren-wk {Γ} {Contexts.[]} ρ η = refl
    ren-wk {Γ} {Γ' Contexts.∷ x} ρ η = cong₂ _,_ 
        (ren-wk (there ∘ᵣ ρ) η) 
        refl  

    sub-wk-lemma2 : ∀ {Γ} (η : ⟦ Γ ⟧-ctx)
        → η ≡ ⟦ idᵣ ⟧-ren η
    sub-wk-lemma2 {Contexts.[]} η = refl
    sub-wk-lemma2 {Γ Contexts.∷ X} (η , v) = cong (_, v) 
        (begin 
        η 
        ≡⟨ sub-wk-lemma2 η ⟩ 
        ⟦ idᵣ ⟧-ren η 
        ≡⟨ ren-wk idᵣ η ⟩ 
        ⟦ there {Y = X} ⟧-ren (η , v) 
        ∎)

    sub-wk-lemma3 : ∀ {Γ Γ' X} {v : ⟦ X ⟧v} (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx) 
        → ⟦ ρ ⟧-ren η ≡ ⟦ ρ ∘ᵣ wkᵣ {X = X} ⟧-ren (η , v)
    sub-wk-lemma3 ρ η = ren-wk ρ η

    sub-V : ∀ { Γ Γ' X  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (v : Γ' ⊢V: X)
        → ⟦ v ⟧-value (⟦ σ ⟧-sub η) ≡ ⟦ v [ σ ]ᵥ ⟧-value η
    sub-V {Γ' = Γ' ∷ X} σ η (var here) = refl
    sub-V {Γ' = Γ' ∷ X} σ η (var (there x)) = sub-V {Γ' = Γ'} (σ ∘ there) η (var x)
    sub-V σ η (sub-value v x) = cong (coerceᵥ x) ((sub-V σ η v))
    sub-V σ η ⟨⟩ = refl
    sub-V σ η ⟨ v , w ⟩ = cong₂ _,_ (sub-V σ η v) (sub-V σ η w)
    sub-V {Γ = Γ} {Γ' = Γ'} σ η (funU {X} m) = fun-ext (λ X' 
        → Eq.trans 
            (cong ⟦ m ⟧-user (cong₂ _,_ 
                (sub-wk σ η) 
                refl))
            (sub-U (extendₛ σ) (η , X') m))

    
    sub-V σ η (funK k) = fun-ext (λ X → 
        Eq.trans
            (cong ⟦ k ⟧-kernel (cong₂ _,_ 
                (sub-wk σ η) 
                refl))
            (sub-K (extendₛ σ) (η , X) k)) 
            --sub-K (extendₛ σ) (η , param) (r op x)
    sub-V σ η (runner r) = fun-ext (λ op → fun-ext (λ x → fun-ext (λ param → 
        begin 
        ⟦ r op x ⟧-kernel (⟦ σ ⟧-sub η , param) 
        ≡⟨ {!   !} ⟩ 
        {!   !} 
        ≡⟨ {!   !} ⟩ 
        ⟦ sub-coop (r op x) σ ⟧-kernel (η , param) 
        ≡⟨ {!   !} ⟩ 
        {!   !}
        )))

{- ⟦ r op x ⟧-kernel (⟦ σ ⟧-sub η , param) ≡
      ⟦ sub-coop (r op x) σ ⟧-kernel (η , param) -}

        {-fun-ext (λ X' 
        → Eq.trans 
            (cong ⟦ m ⟧-user (cong₂ _,_ 
                {!   !}
                {-(begin 
                ⟦ σ ⟧-sub η 
                ≡⟨ {! Eq.sym (sub-ren ? σ η)  !} ⟩ 
                ⟦ {!   !} ⟧-sub (η , X')
                ≡⟨ {! ⟦ wkᵣ ⟧-ren (η , X')  !} ⟩
                {!   !})-}
                    --⟦ (λ x → σ x [ (λ x₁ → there x₁) ]ᵥᵣ) ⟧-sub (η , X')
                refl))
            (sub-U (extendₛ σ) (η , X') m)) -}
    --sub-V {Γ} {Γ' = []} σ η (Terms.funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (Eq.trans refl refl) refl)) (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ} {Γ' = Γ' ∷ x} σ η (Terms.funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (cong₂ _,_ {!   !} {!   !}) refl)) (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ = Γ ∷ x} {Γ' = Γ'} σ η (funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (Eq.trans {!   !} {!   !}) refl)) (sub-U (extendₛ σ) (η , X') m))



    --POTENTIAL TODO 11. 3.: use begin_ syntactic sugar to make the proofs prettier. 


    
    --⟦ σ ⟧-sub η ≡  ⟦ (λ x → σ x [ (λ x₁ → there x₁) ]ᵥᵣ) ⟧-sub (η , X)



    sub-U : ∀ { Γ Γ' Xᵤ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (m : Γ' ⊢U: Xᵤ)
        → ⟦ m ⟧-user (⟦ σ ⟧-sub η) ≡ ⟦ m [ σ ]ᵤ ⟧-user η
    sub-U σ η (sub-user m p) = cong (coerceᵤ p) (sub-U σ η m)
    sub-U σ η (return v) = cong leaf (sub-V σ η v) 
    sub-U σ η (v · w) = cong₂ (λ z → z) (sub-V σ η v) (sub-V σ η w) --ISSUE: How is (λ z → z) accepted?
    sub-U σ η (opᵤ op p par m) = cong₂ (node op p) (sub-V σ η par) (fun-ext (λ res → {! sub-U   !}))
    sub-U σ η (`let m `in n) = cong₂ bind-tree 
        (fun-ext (λ X 
            → Eq.trans 
                (cong ⟦ n ⟧-user (cong₂ _,_ 
                                    (sub-wk σ η)
                                    refl))  
                (sub-U (extendₛ σ) (η , X) n) )) 
        (sub-U σ η m)
    sub-U σ η (match v `with m) = Eq.trans 
        (cong ⟦ m ⟧-user (cong₂ _,_ 
            (cong₂ _,_ 
                (begin 
                ⟦ σ ⟧-sub η 
                ≡⟨ sub-wk σ η ⟩ 
                ⟦ (λ x → σ x [ there ]ᵥᵣ) ⟧-sub (η , _) 
                ≡⟨ sub-wk (there ᵣ∘ₛ σ) (η , _) ⟩ 
                ⟦ (λ x → (there ᵣ∘ₛ σ) x [ there ]ᵥᵣ) ⟧-sub ((η , _ ), _) 
                ∎)
                (cong proj₁ (sub-V σ η v)))   
            (cong proj₂ (sub-V σ η v)))) 
        (sub-U (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ v [ σ ]ᵥ ⟧-value η)) m)
    sub-U σ η (`using r at c `run m finally n) = cong₂ bind-tree 
        {x = (λ { (x , c') → ⟦ n ⟧-user ((⟦ σ ⟧-sub η , x) , c') })}
        {y = (λ { (x , c') → ⟦ n [ extendₛ (extendₛ σ) ]ᵤ ⟧-user ((η , x) , c')})}
        {u = (apply-runner (⟦ r ⟧-value (⟦ σ ⟧-sub η)) (⟦ m ⟧-user (⟦ σ ⟧-sub η)) (⟦ c ⟧-value (⟦ σ ⟧-sub η)))}
        {v = (apply-runner (⟦ r [ σ ]ᵥ ⟧-value η) (⟦ m [ σ ]ᵤ ⟧-user η) (⟦ c [ σ ]ᵥ ⟧-value η))}
            (fun-ext (λ (x , c') →
                begin 
                ⟦ n ⟧-user ((⟦ σ ⟧-sub η , x) , c') 
                ≡⟨ sub-U (extendₛ (extendₛ σ)) {!   !} (`using {!   !} at {! c  !} `run {!   !} finally {!   !}) ⟩ 
                {!   !} 
                ≡⟨ {!   !} ⟩
                {!   !}
                ))
            {!   !}
    sub-U σ η (kernel k at c finally m) = cong₂ bind-tree
        {x = (λ { (X , C) → ⟦ m ⟧-user ((⟦ σ ⟧-sub η , X) , C) })}
        {y = (λ { (X , C) → ⟦ m [ extendₛ (extendₛ σ) ]ᵤ ⟧-user ((η , X) , C) })}
        {u = (⟦ k ⟧-kernel (⟦ σ ⟧-sub η) (⟦ c ⟧-value (⟦ σ ⟧-sub η)))}
        {v = (⟦ k [ σ ]ₖ ⟧-kernel η (⟦ c [ σ ]ᵥ ⟧-value η))}
            (fun-ext (λ (X , C) → Eq.trans 
                (cong ⟦ m ⟧-user (cong₂ _,_ 
                    (cong₂ _,_ 
                        (begin 
                        (⟦ σ ⟧-sub η 
                        ≡⟨ sub-wk {X = {!   !}} σ η ⟩ 
                        ⟦ (λ x → σ x [ there ]ᵥᵣ) ⟧-sub (η , X) 
                        ≡⟨ sub-wk (there ᵣ∘ₛ σ) (η , X) ⟩ 
                        ⟦ (λ x → (there ᵣ∘ₛ σ) x [ there ]ᵥᵣ) ⟧-sub ((η , X) , C)
                        ∎
                        ))
                        refl)
                    refl)) 
                (sub-U (extendₛ (extendₛ σ)) (( η , X) , C) m  ))) 
            (cong₂ (λ a b → a b) 
                {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η)}
                {y = ⟦ k [ σ ]ₖ ⟧-kernel η}
                {u = (⟦ c ⟧-value (⟦ σ ⟧-sub η))}
                {v = (⟦ c [ σ ]ᵥ ⟧-value η)}
                    (sub-K σ η k) 
                    (sub-V σ η c))

    sub-K : ∀ { Γ Γ' Xₖ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (k : Γ' ⊢K: Xₖ)
        → (⟦ k ⟧-kernel (⟦ σ ⟧-sub η)) ≡ (⟦ k [ σ ]ₖ ⟧-kernel η) 
    sub-K σ η (sub-kernel k p) = cong (coerceₖ p) (sub-K σ η k) 
    sub-K σ η (return v) = fun-ext (λ C → cong leaf (cong₂ _,_ (sub-V σ η v) refl))
    sub-K σ η (v · w) = cong₂ (λ x y → x y) (sub-V σ η v) (sub-V σ η w)
    sub-K σ η (`let k `in l) = fun-ext (λ c → cong₂ bind-tree 
        (fun-ext (λ (X , C') → cong₂ (λ a b → a b) 
            {x = ⟦ l ⟧-kernel (⟦ σ ⟧-sub η , X)}
            {y = ⟦ l [ extendₛ σ ]ₖ ⟧-kernel (η , X)}
            {u = C'}
            {v = C'}
                (sub-K (extendₛ σ) (η , X) {! l  !})
                refl)) 
        (cong₂ (λ x y → x y) 
            (sub-K σ η k) 
            refl)) 

    sub-K σ η (match v `with k) = Eq.trans 
        (cong ⟦ k ⟧-kernel 
            (cong₂ _,_ 
                (cong₂ _,_
                    (begin 
                    ⟦ σ ⟧-sub η 
                    ≡⟨ sub-wk σ η ⟩ 
                    ⟦ (λ x → σ x [ there ]ᵥᵣ) ⟧-sub (η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η))
                    ≡⟨ sub-wk (there ᵣ∘ₛ σ) (η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) ⟩ 
                    ⟦ (λ x → (σ x [ (λ x₁ → there x₁) ]ᵥᵣ) [ (λ x₁ → there x₁) ]ᵥᵣ) ⟧-sub
                        ((η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ v [ σ ]ᵥ ⟧-value η)) 
                    ∎) 
                    (cong proj₁ (sub-V σ η v))) (cong proj₂ (sub-V σ η v)) )) 
                (sub-K (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ v [ σ ]ᵥ ⟧-value η)) k)
    sub-K σ η (opₖ op p par k) = fun-ext 
        (λ C → cong₂ (node op p) 
            (sub-V σ η par) 
            (fun-ext 
                (λ res → cong₂ (λ k C → k C) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , res)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , res)} 
                    (Eq.trans 
                        (cong ⟦ k ⟧-kernel (cong₂ _,_ (sub-wk σ η) refl))  
                        (sub-K (extendₛ σ) (η , res) k)) 
                    refl)))  
    sub-K σ η (getenv k) = fun-ext 
        (λ C → cong₂ (λ a b → a b) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , C)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , C)} {u = C} {v = C} 
            (Eq.trans 
                (cong ⟦ k ⟧-kernel (cong₂ _,_ (sub-wk σ η) refl))  
                (sub-K (extendₛ σ) (η , C) k)) 
            refl) 
    sub-K σ η (setenv c k) = fun-ext (λ x → {! cong₂ (λ a b → a b) {x = ⟦ setenv c k ⟧-kernel} {y = ?} {u = (⟦ σ ⟧-sub η)} {v = (⟦ c [ σ ]ᵥ ⟧-value η)}  
        ? 
        ?  !})
    sub-K σ η (user m `with k) = fun-ext (λ C → 
        cong₂ bind-tree 
            (fun-ext (λ X → 
                cong₂ (λ a b → a b) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , X)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , X)} 
                    (Eq.trans 
                        (cong ⟦ k ⟧-kernel 
                            (cong₂ _,_ 
                                (sub-wk σ η)
                                refl))
                        (sub-K (extendₛ σ) (η , X) k))
                    refl)) 
            (sub-U σ η m)) 
                      
                               