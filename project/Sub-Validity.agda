{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using ( _≡⟨⟩_ ; _∎ ) renaming (begin_ to start_ ; step-≡ to step-= ) 
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

    sub-double : ∀ { Γ Γ' X Xᵤ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (m : (Γ' ∷ X) ⊢U: Xᵤ) (X' : ⟦ X ⟧v) 
        → ⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ wkᵣ ]ᵥᵣ) ⟧-sub (η , X')
    sub-double {Γ} {Contexts.[]} {X} {Xᵤ} σ η m X' = refl
    sub-double {Γ} {Γ' Contexts.∷ x} {X} {Xᵤ} σ η m X' = cong₂ _,_ {! (sub-double ? η ? X') !} {! cong₂ _,_  !}

    sub-there : ∀ { Γ Γ' _ } (σ : Sub Γ (Γ' ∷ _)) (η : ⟦ Γ ⟧-ctx) 
        → ⟦ σ here ⟧-value η ≡ ⟦ σ here [ (λ x → (there x)) ]ᵥᵣ ⟧-value (η , _)
    sub-there {Γ} {Γ'} {x} σ η = {! αmma  !}

    sub-weakening : ∀ { Γ Γ' g } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) 
        → ⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ wkᵣ ]ᵥᵣ)  ⟧-sub {! (η , g) !}
    sub-weakening {Γ} {Γ'} {g} σ η = {!   !}
    --sub-weakening {Γ} {[]} {g} σ η = refl
    --sub-weakening {Γ} {Γ' ∷ x} {g} σ η = cong₂ _,_ (sub-weakening {Γ} {Γ'} (λ x → σ (there x)) η) {!  !}



    ren-sub : ∀ { Γ Γ' Γ'' g } (ρ : Ren Γ Γ') (σ : Sub Γ' Γ'') (η : ⟦ Γ ⟧-ctx) 
        → ⟦ σ ⟧-sub (⟦ ρ ⟧-ren {! η , ?  !}) ≡ ⟦ ρ ᵣ∘ₛ σ ⟧-sub {!   !}
    ren-sub {Γ} {Γ'} {[]} ρ σ η = {!   !}
    ren-sub {Γ} {Γ'} {Γ'' ∷ x} ρ σ η = {!   !} --cong₂ _,_ (ren-sub ρ (λ x → σ (there x)) η) {!  ⟦ wkᵣ ⟧-ren η  !}

    sub-weakening' : ∀ { Γ Γ' g v} (σ : Sub Γ (Γ' ∷ v)) (η : ⟦ Γ ⟧-ctx) 
        → ⟦ σ ⟧-sub η ≡ ⟦ wkᵣ ᵣ∘ₛ σ  ⟧-sub (η , g)
    sub-weakening' {Γ} {Γ'} {g} {v} σ η = Eq.trans (cong₂ _,_ {!   !} (Eq.trans {!   !} {!   !} )  ) (ren-sub wkᵣ σ (η , g))



    sub-V : ∀ { Γ Γ' X  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (v : Γ' ⊢V: X)
        → ⟦ v ⟧-value (⟦ σ ⟧-sub η) ≡ ⟦ v [ σ ]ᵥ ⟧-value η
    sub-V {Γ' = Γ' ∷ X} σ η (var here) = refl
    sub-V {Γ' = Γ' ∷ X} σ η (var (there x)) = sub-V {Γ' = Γ'} (σ ∘ there) η (var x)
    sub-V σ η (sub-value v x) = cong (coerceᵥ x) ((sub-V σ η v))
    sub-V σ η ⟨⟩ = refl
    sub-V σ η ⟨ v , w ⟩ = cong₂ _,_ (sub-V σ η v) (sub-V σ η w)


    sub-V {Γ = Γ} {Γ' = Γ'} σ η (funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (sub-double σ η m X') refl)) (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ} {Γ' = []} σ η (Terms.funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (Eq.trans refl refl) refl)) (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ} {Γ' = Γ' ∷ x} σ η (Terms.funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (cong₂ _,_ {!   !} {!   !}) refl)) (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ = Γ ∷ x} {Γ' = Γ'} σ η (funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (Eq.trans {!   !} {!   !}) refl)) (sub-U (extendₛ σ) (η , X') m))




    
    sub-V σ η (funK k) = fun-ext (λ X → {! sub-K (extendₛ σ) (η , X) k  !}) 
    sub-V σ η (runner r) = {!   !}

    sub-U : ∀ { Γ Γ' Xᵤ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (m : Γ' ⊢U: Xᵤ)
        → ⟦ m ⟧-user (⟦ σ ⟧-sub η) ≡ ⟦ m [ σ ]ᵤ ⟧-user η
    sub-U σ η (sub-user m p) = cong (coerceᵤ p) (sub-U σ η m)
    sub-U σ η (return v) = cong leaf (sub-V σ η v) 
    sub-U σ η (v · w) = cong₂ (λ z → z) (sub-V σ η v) (sub-V σ η w) --ISSUE: How is (λ z → z) accepted?
    sub-U σ η (opᵤ op p par m) = cong₂ (node op p) (sub-V σ η par) (fun-ext (λ res → {! sub-U   !}))
    sub-U σ η (`let m `in n) = cong₂ bind-tree (fun-ext (λ X → Eq.trans (cong ⟦ n ⟧-user (cong₂ _,_ ((sub-double σ η n X)) refl))  (sub-U (extendₛ σ) (η , X) n) )) (sub-U σ η m)
    sub-U σ η (match v `with m) = Eq.trans (cong ⟦ m ⟧-user {!   !}) 
        (sub-U (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ v [ σ ]ᵥ ⟧-value η)) m)
    sub-U σ η (`using r at c `run m finally n) = {! cong₂  bind-tree ? ?   !}
    sub-U σ η (kernel k at c finally m) = {!   !}

    sub-K : ∀ { Γ Γ' Xₖ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (k : Γ' ⊢K: Xₖ)
        → (⟦ k ⟧-kernel (⟦ σ ⟧-sub η)) ≡ (⟦ k [ σ ]ₖ ⟧-kernel η) 
    sub-K σ η (sub-kernel k p) = cong (coerceₖ p) (sub-K σ η k) 
    sub-K σ η (return v) = fun-ext (λ C → cong leaf (cong₂ _,_ (sub-V σ η v) refl))
    sub-K σ η (v · w) = cong₂ (λ x y → x y) (sub-V σ η v) (sub-V σ η w)
    sub-K σ η (`let k `in l) = fun-ext (λ c → cong₂ bind-tree {! ((cong₂ (λ x C' → x C') ? refl))  !} (cong₂ (λ x y → x y) (sub-K σ η k) refl)) 
    --(cong₂ (λ x y → x y) {x = ?} {u = c} (fun-ext ?) refl)
    --⟦ `let k `in l ⟧-kernel (⟦ σ ⟧-sub η) c ≡
    --⟦ `let k `in l [ σ ]ₖ ⟧-kernel η c

    --(cong ⟦ k ⟧-kernel (cong₂ _,_ (cong₂ _,_ (Eq.trans (sub-weakening σ η) (sub-weakening (λ x → σ x [ there ]ᵥᵣ) (η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)))) {! cong (λ x → proj₁ x)   !}) {!   !})) 
    sub-K σ η (match v `with k) = Eq.trans 
        (cong ⟦ k ⟧-kernel 
            (cong₂ _,_ 
                (cong₂ _,_
                    {!   !} 
                    --(Eq.trans 
                        --{! (sub-weakening σ η)  !} 
                        --{! (sub-weakening (λ x → σ x [ (λ x₁ → there x₁) ]ᵥᵣ) (η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)))  !} )  
                    {! cong (λ x → proj₁ x)   !}) (cong proj₂ (sub-V σ η v)) )) 
                (sub-K (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ v [ σ ]ᵥ ⟧-value η)) k)
    sub-K σ η (opₖ op p par k) = fun-ext 
        (λ C → cong₂ (node op p) 
            (sub-V σ η par) 
            (fun-ext 
                (λ res → cong₂ (λ k C → k C) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , res)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , res)} 
                    (Eq.trans 
                        (cong ⟦ k ⟧-kernel (cong₂ _,_ {! (sub-weakening σ η)  !} refl))  
                        (sub-K (extendₛ σ) (η , res) k)) 
                    refl)))  
    sub-K σ η (getenv k) = fun-ext 
        (λ C → cong₂ (λ a b → a b) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , C)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , C)} {u = C} {v = C} 
            (Eq.trans 
                (cong ⟦ k ⟧-kernel (cong₂ _,_ {! (sub-weakening σ η)  !} refl))  
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
                                (sub-weakening σ η)
                                refl))
                        (sub-K (extendₛ σ) (η , X) k)) 
                    refl)) 
            (sub-U σ η m)) 
  