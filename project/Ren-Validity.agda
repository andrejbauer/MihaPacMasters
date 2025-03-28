{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning     

open import Function

import Contexts
open import Parameters
import Types
import Terms
import Monads
import Equations
import Denotations

module Ren-Validity (G : GTypes) (O : Ops G) where

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

ren-coop-lemma : ∀ { Γ Γ' Σ C op} (ρ : Ren Γ Γ') (coop : co-op Γ' Σ C op)
    → coop [ extendᵣ ρ ]ₖᵣ ≡ rename-coop coop ρ
ren-coop-lemma ρ (sub-kernel coop x) = refl
ren-coop-lemma ρ (return x) = refl
ren-coop-lemma ρ (x · x₁) = refl
ren-coop-lemma ρ (`let coop `in coop₁) = refl
ren-coop-lemma ρ (match x `with coop) = refl
ren-coop-lemma ρ (opₖ op₁ x x₁ coop) = refl
ren-coop-lemma ρ (getenv coop) = refl
ren-coop-lemma ρ (setenv x coop) = refl
ren-coop-lemma ρ (user x `with coop) = refl

mutual 

    ⟦_⟧-ren : ∀ {Γ Γ'} → Ren Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx
    ⟦_⟧-ren {Γ' = []} ρ η = tt
    ⟦_⟧-ren {Γ' = Γ' ∷ X} ρ η = ⟦ ρ ∘ there ⟧-ren η , lookup (ρ here) η

    ren-wk : ∀ {Γ Γ' X} {v : ⟦ X ⟧v} (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx) 
        → ⟦ ρ ⟧-ren η ≡ ⟦ ρ ∘ᵣ there {Y = X} ⟧-ren (η , v)
    ren-wk {Γ} {Contexts.[]} ρ η = refl
    ren-wk {Γ} {Γ' Contexts.∷ x} ρ η = cong₂ _,_ 
        (ren-wk (there ∘ᵣ ρ) η) 
        refl 

    ren-id-lemma : ∀ {Γ} (η : ⟦ Γ ⟧-ctx)
        → η ≡ ⟦ idᵣ ⟧-ren η
    ren-id-lemma {Contexts.[]} η = refl
    ren-id-lemma {Γ Contexts.∷ X} (η , v) = cong (_, v)
        (begin 
        η 
        ≡⟨ ren-id-lemma η ⟩ 
        ⟦ idᵣ ⟧-ren η 
        ≡⟨ ren-wk idᵣ η ⟩ 
        ⟦ there {Y = X} ⟧-ren (η , v) 
        ∎)


    ren-env : ∀ {Γ Γ' X} {ρ : Ren Γ Γ'} {η : ⟦ Γ ⟧-ctx} → (x : X ∈ Γ') 
        → lookup x (⟦ ρ ⟧-ren η) ≡ lookup (ρ x) η
    ren-env {Γ} {Γ'} {X} {ρ} {η} here = refl
    ren-env {Γ} {Γ'} {X} {ρ} {η} (there x) = ren-env {ρ = ρ ∘ there} x

    lookup-ext : ∀ {Γ} {η η' : ⟦ Γ ⟧-ctx} → (∀ {X} (x : X ∈ Γ) 
        → lookup x η ≡ lookup x η') → η ≡ η'
    lookup-ext {[]} {η} {η'} eq = refl
    lookup-ext {Γ ∷ X} {η , v} {η' , v'} eq = cong₂ _,_ (lookup-ext (eq ∘ there))  (eq here)

    ren-value : ∀ { Γ Γ' X} (V : Γ' ⊢V: X) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ V ⟧-value (⟦ ρ ⟧-ren η) ≡ ⟦ V [ ρ ]ᵥᵣ ⟧-value η
    ren-value {Γ} {Γ'} (var x) ρ η = lookup-ren x ρ η
    ren-value {Γ} {Γ'} (sub-value V x) ρ η = cong (coerceᵥ x) (ren-value V ρ η) 
    ren-value {Γ} {Γ'} ⟨⟩ ρ η = refl
    ren-value {Γ} {Γ'} ⟨ V , W ⟩ ρ η = cong₂ _,_ (ren-value V ρ η) (ren-value W ρ η) 
    ren-value {Γ} {Γ'} (funU x) ρ η = fun-ext (λ X 
        → cong₂ (λ a b → a b) {x =  ⟦ funU x ⟧-value (⟦ ρ ⟧-ren η)} {y = ⟦ funU x [ ρ ]ᵥᵣ ⟧-value η} 
            (fun-ext (λ Y → 
                Eq.trans 
                    (cong ⟦ x ⟧-user (cong₂ _,_ 
                        (ren-wk {v = Y} ρ η)
                        refl))
                    (ren-user x (extendᵣ ρ) (η , Y))))  
            refl)
    ren-value {Γ} {Γ'} (funK x) ρ η = fun-ext (λ X → 
        Eq.trans 
            (cong ⟦ x ⟧-kernel (cong₂ _,_ 
                (ren-wk {v = X} ρ η)
                refl)) 
            (ren-kernel x (extendᵣ ρ) (η , X)))
    ren-value {Γ} {Γ'} (runner x) ρ η = fun-ext (λ op → fun-ext (λ x' → fun-ext (λ param → 
        begin 
        ⟦ x op x' ⟧-kernel (⟦ ρ ⟧-ren η , param) 
        ≡⟨ cong ⟦ x op x' ⟧-kernel (cong₂ _,_ 
            (ren-wk ρ η)
            refl) ⟩ 
        ⟦ x op x' ⟧-kernel (⟦ extendᵣ {X = {! _ !}} ρ ⟧-ren (η , param)) 
        ≡⟨ (ren-kernel (x op x') (extendᵣ ρ) (η , param)) ⟩ 
        ⟦ x op x' [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , param) 
        ≡⟨ cong₂ (λ a b → a b) 
                {x = ⟦ x op x' [ extendᵣ ρ ]ₖᵣ ⟧-kernel}
                {y = ⟦ rename-coop (x op x') ρ ⟧-kernel}
                {u = η , param}
                {v = η , param}
                (cong ⟦_⟧-kernel 
                    {x = x op x' [ extendᵣ ρ ]ₖᵣ} 
                    {y = rename-coop (x op x') ρ} 
                    (ren-coop-lemma ρ (x op x')))
                refl ⟩ 
        refl)))

    ren-user : ∀ { Γ Γ' Xᵤ} (M : Γ' ⊢U: Xᵤ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ M ⟧-user (⟦ ρ ⟧-ren η) ≡ ⟦ M [ ρ ]ᵤᵣ ⟧-user η
    ren-user {Γ} {Γ'} {Xᵤ} (sub-user M p) ρ η = cong (coerceᵤ p) (ren-user M ρ η) 
    ren-user {Γ} {Γ'} {Xᵤ} (return V) ρ η = cong leaf (ren-value V ρ η)
    ren-user {Γ} {Γ'} {Xᵤ} (V · W) ρ η = cong₂ (λ a b → a b) (ren-value V ρ η) (ren-value W ρ η) 
    ren-user {Γ} {Γ'} {Xᵤ} (opᵤ op x par M) ρ η = cong₂ (node op x) 
        (ren-value par ρ η) 
        (fun-ext (λ res → Eq.trans 
                (cong ⟦ M ⟧-user (cong₂ _,_
                    (ren-wk {v = res} ρ η)
                    refl))
                (ren-user M (extendᵣ ρ) (η , res)))) 
    ren-user {Γ} {Γ'} {Xᵤ} (`let M `in N) ρ η = cong₂ bind-tree 
        (fun-ext (λ X → Eq.trans
            (cong ⟦ N ⟧-user (cong₂ _,_
                (ren-wk {v = X} ρ η)
                refl))
            (ren-user N (extendᵣ ρ) (η , X)))) 
        (ren-user M ρ η)
    ren-user {Γ} {Γ'} {Xᵤ} (match V `with M) ρ η = 
        begin 
        (⟦ M ⟧-user ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) , proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η)))
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ 
            {v = proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)} 
            (cong₂ _,_ 
                refl
                (cong proj₁ (ren-value V ρ η)))
            (cong proj₂ (ren-value V ρ η))) ⟩
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
        ⟦ M ⟧-user (⟦ extendᵣ (extendᵣ ρ) ⟧-ren ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))
        ≡⟨ ren-user M (extendᵣ (extendᵣ ρ)) ((η , (proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) , (proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) ⟩ 
        refl)
    ren-user {Γ} {Γ'} {Xᵤ} (`using R at C `run M finally N) ρ η = cong₂ bind-tree
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
                ≡⟨ ren-user N (extendᵣ (extendᵣ ρ)) ((η , x) , c') ⟩ 
                refl)}))
{- ⟦ N ⟧-user ((⟦ ρ ⟧-ren η , x) , c')
≡ 
⟦ N [ extendᵣ (extendᵣ ρ) ]ᵤᵣ ⟧-user ((η , x) , c') -}
        (begin 
            apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C ⟧-value (⟦ ρ ⟧-ren η)) 
            ≡⟨ cong (apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η))) (ren-value C ρ η) ⟩ 
            apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C [ ρ ]ᵥᵣ ⟧-value η) 
            ≡⟨ cong₂ (λ a b → apply-runner a b (⟦ C [ ρ ]ᵥᵣ ⟧-value η)) 
                {x = (⟦ R ⟧-value (⟦ ρ ⟧-ren η))}
                {y = (⟦ R [ ρ ]ᵥᵣ ⟧-value η)}
                {u = (⟦ M ⟧-user (⟦ ρ ⟧-ren η))}
                {v = (⟦ M [ ρ ]ᵤᵣ ⟧-user η)}
                (ren-value R ρ η) 
                (ren-user M ρ η) ⟩ 
            apply-runner (⟦ R [ ρ ]ᵥᵣ ⟧-value η) (⟦ M [ ρ ]ᵤᵣ ⟧-user η) (⟦ C [ ρ ]ᵥᵣ ⟧-value η) 
        ∎)

    ren-user {Γ} {Γ'} {Xᵤ} (kernel K at C finally M) ρ η = cong₂ bind-tree 
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
            ≡⟨ ren-user M (extendᵣ (extendᵣ ρ)) ((η , X) , C) ⟩ 
            refl 
        ))
{- ⟦ M ⟧-user ((⟦ ρ ⟧-ren η , X) , C) ≡ ⟦ M [ extendᵣ (extendᵣ ρ) ]ᵤᵣ ⟧-user ((η , X) , C) -}
        (cong₂ (λ a b → a b) 
            (ren-kernel K ρ η) 
            (ren-value C ρ η)) 


    ren-kernel : ∀ { Γ Γ' Xₖ} (K : Γ' ⊢K: Xₖ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) ≡ ⟦ K [ ρ ]ₖᵣ ⟧-kernel η
    ren-kernel {Γ} {Γ'} {Xₖ} (sub-kernel K p) ρ η = cong (coerceₖ p) (ren-kernel K ρ η)
    ren-kernel {Γ} {Γ'} {Xₖ} (return V) ρ η = fun-ext (λ C → cong leaf (cong₂ _,_ (ren-value V ρ η) refl))  
    ren-kernel {Γ} {Γ'} {Xₖ} (var x · W) ρ η = cong₂ (λ a b → a b) 
        {x = lookup x (⟦ ρ ⟧-ren η)}{y = lookup (ρ x) η} 
        {u = ⟦ W ⟧-value (⟦ ρ ⟧-ren η)}{v = ⟦ W [ ρ ]ᵥᵣ ⟧-value η} 
        (lookup-ren x ρ η) 
        (ren-value W ρ η) 
    ren-kernel {Γ} {Γ'} {Xₖ} (sub-value V x · W) ρ η = cong₂ (λ a b → a b) 
        {x = coerceᵥ x (⟦ V ⟧-value (⟦ ρ ⟧-ren η))}{y = coerceᵥ x (⟦ V [ ρ ]ᵥᵣ ⟧-value η)}
        {u = ⟦ W ⟧-value (⟦ ρ ⟧-ren η)} {v = ⟦ W [ ρ ]ᵥᵣ ⟧-value η} 
        (cong (coerceᵥ x) (ren-value V ρ η)) 
        (ren-value W ρ η) 
    ren-kernel {Γ} {Γ'} {Xₖ} (funK K · W) ρ η = 
        begin 
        (⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , ⟦ W ⟧-value (⟦ ρ ⟧-ren η)) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_ 
            (ren-wk ρ η)
            (ren-value W ρ η) ) ⟩ 
        ⟦ K ⟧-kernel (⟦ extendᵣ ρ ⟧-ren (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η))
        ≡⟨ refl ⟩ 
        ⟦ K ⟧-kernel (⟦ extendᵣ ρ ⟧-ren (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η)) 
        ≡⟨ ren-kernel K (extendᵣ ρ) (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η) ⟩ 
        refl)
    ren-kernel {Γ} {Γ'} {Xₖ} (`let K `in L) ρ η = fun-ext (λ C → cong₂ bind-tree
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
            ⟦ L ⟧-kernel (⟦ extendᵣ {X = {!   !}} ρ ⟧-ren (η , x')) C' 
            ≡⟨ cong₂ (λ a b → a b) 
                (ren-kernel L (extendᵣ ρ) (η , x')) 
                refl ⟩ 
            (⟦ L [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , x') C') 
            ≡⟨ refl ⟩ 
            refl 
            ))
        (cong₂ (λ a b → a b) (ren-kernel K ρ η) refl))
    ren-kernel {Γ} {Γ'} {Xₖ} (match V `with K) ρ η = 
        begin 
        (⟦ K ⟧-kernel ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) , proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_
            (cong₂ _,_ 
                refl 
                (cong proj₁ (ren-value V ρ η)))
            (cong proj₂ (ren-value V ρ η))) ⟩ 
        ⟦ K ⟧-kernel (((⟦ ρ ⟧-ren η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_ 
            (cong₂ _,_ 
                (Eq.trans
                    (ren-wk ρ η)
                    (ren-wk (ρ ∘ᵣ there) (η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))) 
                refl) 
            refl) ⟩
        ⟦ K ⟧-kernel (⟦ extendᵣ {X = {!   !}} 
            (extendᵣ {X = {!   !}} ρ) ⟧-ren 
            ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))  
        ≡⟨ ren-kernel K (extendᵣ (extendᵣ ρ)) ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) ⟩ 
        ⟦ K [ extendᵣ (extendᵣ ρ) ]ₖᵣ ⟧-kernel ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) 
        ≡⟨ refl ⟩ 
        refl)
{- ⟦ K ⟧-kernel
      ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) ,
       proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η)))  ≡ 
    ⟦ K [ extendᵣ (extendᵣ ρ) ]ₖᵣ ⟧-kernel
      ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) ,
       proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) -}
    ren-kernel {Γ} {Γ'} {Xₖ} (opₖ op x par K) ρ η = fun-ext (λ C → 
        cong₂ (node op x) 
            (ren-value par ρ η) 
            (fun-ext (λ res → cong₂ (λ a b → a b)
                {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , res)}
                {y = ⟦ K [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , res)}
                (Eq.trans 
                    (cong ⟦ K ⟧-kernel (cong₂ _,_
                        (ren-wk ρ η)
                        refl)) 
                    (ren-kernel K (extendᵣ ρ) (η , res))) 
                refl)))
    ren-kernel {Γ} {Γ'} {Xₖ} (getenv K) ρ η = fun-ext (λ C → 
        cong₂ (λ a b → a b) 
            {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , C)}
            {y = ⟦ K [ extendᵣ ρ ]ₖᵣ ⟧-kernel (η , C)}
            (Eq.trans 
                (cong ⟦ K ⟧-kernel (cong₂ _,_ 
                    (ren-wk ρ η)
                    refl))
                (ren-kernel K (extendᵣ ρ) (η , C))) 
            refl)
    ren-kernel {Γ} {Γ'} {Xₖ} (setenv V K) ρ η = fun-ext (λ _ → 
        cong₂ (λ a b → a b) 
        {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η)}
        {y = ⟦ K [ ρ ]ₖᵣ ⟧-kernel η} 
        (ren-kernel K ρ η) 
        (ren-value V ρ η))
    ren-kernel {Γ} {Γ'} {Xₖ} (user M `with K) ρ η = fun-ext (λ C → 
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
                    (ren-kernel K (extendᵣ ρ) (η , X')))
                refl)
            (ren-user M ρ η))

    --lookup-ren
    lookup-ren : ∀ { Γ Γ' v} (x : v ∈ Γ') (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → lookup x (⟦ ρ ⟧-ren η) ≡ lookup (ρ x) η
    lookup-ren here ρ η = refl
    lookup-ren (there x) ρ η = lookup-ren x (λ x → ρ (there x)) η