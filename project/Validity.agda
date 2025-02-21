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

module Validity (G : GTypes) (O : Ops G) where

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
        → ⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ wkᵣ ]ᵥᵣ)  ⟧-sub (η , g)
    sub-weakening {Γ} {[]} {g} σ η = refl
    sub-weakening {Γ} {Γ' ∷ x} {g} σ η = cong₂ _,_ (sub-weakening {Γ} {Γ'} (λ x → σ (there x)) η) {!  !}

    sub-weakening' : ∀ { Γ Γ' g v} (σ : Sub Γ (Γ' ∷ v)) (η : ⟦ Γ ⟧-ctx) 
        → ⟦ σ here ⟧-value η ≡ ⟦ σ here [ wkᵣ ]ᵥᵣ ⟧-value (η , g)
    sub-weakening' {Γ} {Γ'} {g} {v} σ η = {! sub-weakening ? ? !}

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
                    (Eq.trans 
                        {! (sub-weakening σ η)  !} 
                        {! (sub-weakening (λ x → σ x [ (λ x₁ → there x₁) ]ᵥᵣ) (η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)))  !} )  
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


    {- valid-V : ∀ {Γ : Ctx} {X : VType} {v w : Γ ⊢V: X} → (Γ ⊢V v ≡ w) → ∀ η → ⟦ v ⟧-value η ≡ ⟦ w ⟧-value η
    valid-U : ∀ {Γ : Ctx} {Xᵤ : UType} {m n : Γ ⊢U: Xᵤ} → (Γ ⊢U m ≡ n) → ∀ η → ⟦ m ⟧-user η ≡ ⟦ n ⟧-user η
    valid-K : ∀ {Γ : Ctx} {Xₖ : KType} {k l : Γ ⊢K: Xₖ} → (Γ ⊢K k ≡ l) → ∀ η → ⟦ k ⟧-kernel η ≡ ⟦ l ⟧-kernel η

    valid-V refl η = Eq.refl
    valid-V (sym eq-v) η = Eq.sym (valid-V eq-v η)
    valid-V (trans eq-v eq-w) η = Eq.trans (valid-V eq-v η) (valid-V eq-w η)
    valid-V (prod-cong eq-v eq-w) η = Eq.cong₂ _,_ (valid-V eq-v η) (valid-V eq-w η)
    valid-V (fun-cong eq-m) η = fun-ext (λ x → valid-U eq-m (η , x)) --fun-ext (λ x → valid-U eq (η , x))
    valid-V (funK-cong eq-k) η = fun-ext (λ x → valid-K eq-k (η , x))  --fun-ext (λ x → valid-K refl η) 
    valid-V (runner-cong eq-k) η = fun-ext (λ op → fun-ext (λ p → fun-ext (λ param → valid-K (eq-k op p) (η , param)))) --fun-ext (λ op → fun-ext (λ p → fun-ext (λ param → valid-K refl η)))
    valid-V unit-eta η = refl
    valid-V {w = w} funU-eta η = Eq.sym {! sub-V   !} --Relies on substitution (complete mystery for now)
    valid-V funK-eta η = {!   !} --fun-ext (λ x → valid-K refl η) --Relies on substitution (complete mystery for now)




    valid-U refl η = Eq.refl
    valid-U (sym eq-m) η = Eq.sym (valid-U eq-m η) 
    valid-U (trans eq-m eq-n) η = Eq.trans (valid-U eq-m η) (valid-U eq-n η) 
    valid-U (return-cong eq-v) η = Eq.cong (λ x → leaf x) (valid-V eq-v η)
    valid-U {Γ} {Xᵤ} {m} {n} (·-cong eq-v eq-w) η = cong₂ (λ v-value w-value → v-value w-value) (valid-V eq-v η) (valid-V eq-w η)
    valid-U (opᵤ-cong p eq-v eq-m) η = cong₂ (node _ p) (valid-V eq-v η) (fun-ext (λ res → valid-U eq-m (η , res))) 
    valid-U (let-in-cong eq-m eq-n) η = cong₂ bind-user (fun-ext (λ x → valid-U eq-n (η , x))) (valid-U eq-m η)
    valid-U (match-with-cong eq-v eq-m) η = cong₂ (λ m η' → m η') (fun-ext (λ η' → valid-U eq-m η')) (cong (λ x → ( η , proj₁ x) , proj₂ x) (valid-V eq-v η))
    valid-U (using-at-run-finally-cong eq-r eq-w eq-m eq-n) η = 
        cong₂ bind-tree (fun-ext (λ η' → valid-U eq-n ((η , proj₁ η') , proj₂ η') ))  
            (cong₂ (λ r,m w → apply-runner (proj₁ r,m) (proj₂ r,m) w)  (cong₂ (λ r m → r , m)  (valid-V eq-r η) (valid-U eq-m η)) (valid-V eq-w η))
    valid-U (kernel-at-finally-cong eq-v eq-m eq-k) η = 
        cong₂ bind-tree (fun-ext (λ x → valid-U eq-m ((η , proj₁ x) , proj₂ x))) (cong₂ (λ k c → k c ) (valid-K eq-k η) (valid-V eq-v η))


    valid-U (funU-beta m v) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ sub-var refl)) (sub-U (var ∷ₛ v) η m) --Relies on substitution (complete mystery for now)



    valid-U (let-in-beta-return_ v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ sub-var refl)) (sub-U (var ∷ₛ v) η m) --Relies on substitution (complete mystery for now)


    valid-U (let-in-beta-op op p param m n) η = cong (node op p (⟦ param ⟧-value η)) 
        (fun-ext 
        (λ res → cong₂ bind-tree (fun-ext (λ x₁ → Eq.trans (cong ⟦ n ⟧-user (cong₂ _,_ {!   !} refl)) (sub-U (extendₛ (λ p₁ → var (there p₁))) ((η , res) , x₁) n))) refl))
        --cong (node op p (⟦ param ⟧-value η)) (fun-ext (λ res → cong₂ bind-tree (fun-ext (λ X₁ → {!   !})) refl)) --Relies on substitution (complete mystery for now)
        

    valid-U (match-with-beta-prod v w m) η = Eq.trans {!    !} (sub-U ((var ∷ₛ v) ∷ₛ w) η m) --Relies on substitution (complete mystery for now)
        --ALMOST COMPLETED


    valid-U (using-run-finally-beta-return r w v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (cong₂ _,_ sub-var refl) refl))
        (sub-U ((var ∷ₛ v) ∷ₛ w) η m) --Relies on substitution (complete mystery for now)
    {-
    ⟦ m ⟧-user ((η , ⟦ v ⟧-value η) , ⟦ w ⟧-value η) ≡
      ⟦ m [ (var ∷ₛ v) ∷ₛ w ]ᵤ ⟧-user η
      This repeated between the previous two examples
    ⟦ m ⟧-user ((η , ⟦ v ⟧-value η) , ⟦ w ⟧-value η) ≡
      ⟦ m [ (var ∷ₛ v) ∷ₛ w ]ᵤ ⟧-user η
    -}

    valid-U (using-run-finally-beta-op R w op param p m n) η = {! cong₂ bind-tree ? (cong₂ bind-tree ? (Eq.trans ? (sub-U )   !} --Relies on substitution (complete mystery for now)
    valid-U (kernel-at-finally-beta-return v c n) η = Eq.trans (cong ⟦ n ⟧-user {!   !}) (sub-U ((var ∷ₛ v) ∷ₛ c) η n) --Relies on substitution (complete mystery for now)
    valid-U (kernel-at-finally-beta-getenv c k m) η = {! cong (bind-tree _) (sub-K )  !} --Relies on substitution (complete mystery for now)
    valid-U (kernel-at-finally-setenv c c' k m) η = {!   !} --refl --Strange
    valid-U (kernel-at-finally-beta-op op p param c k m) η = {!  !} --Relies on substitution (complete mystery for now)
    
    valid-U (let-in-eta-M n) η = {!   !} 
        --Eq.cong-app refl (⟦ n ⟧-user η) 
        --bind-tree (λ X₁ → leaf X₁) (⟦ n ⟧-user η) ≡ ⟦ n ⟧-user η

    valid-K refl η = Eq.refl
    valid-K (sym eq-k) η = Eq.sym (valid-K eq-k η)
    valid-K (trans eq-k eq-l) η = Eq.trans (valid-K eq-k η) (valid-K eq-l η) 
    valid-K (return-cong eq-v) η = fun-ext (λ x → cong leaf (cong (λ y → (y , x)) (valid-V eq-v η))) 
    valid-K (·-cong eq-v eq-w) η = cong₂ (λ v-value w-value → v-value w-value) (valid-V eq-v η) (valid-V eq-w η) 
    valid-K (let-in-cong eq-k eq-l) η = 
        fun-ext (λ c → cong₂ bind-tree (fun-ext (λ x → cong (λ x₁ → x₁ (proj₂ x)) (valid-K eq-l (η , proj₁ x) )) )  (cong₂ (λ a b → a b) (valid-K eq-k η) refl) )
    valid-K (match-with-cong eq-v eq-k) η = cong₂ (λ k v → k v) (fun-ext (λ η' → valid-K eq-k η' )) (cong (λ v → (( η , proj₁ v ) , proj₂ v)) (valid-V eq-v η))
    valid-K (opₖ-cong {V} {W} {Σ} {C} {op} {p} {param} eq-v eq-k) η = fun-ext (λ _ → cong₂ (node op p) (valid-V eq-v η) (fun-ext (λ res → cong₂ (λ k≡k' c → k≡k' c) (valid-K eq-k (η , res))  refl ))) 
    --TODO 28. 01. : change the names of these variables to be appropriate to what they represent
    valid-K (getenv-cong eq-k) η = fun-ext (λ c → cong₂ (λ k≡k' c' → k≡k' c') (valid-K eq-k (η , c)) refl)
    --TODO 28. 01. : change the names of these variables to be appropriate to what they represent
    valid-K (setenv-cong eq-v eq-k) η = fun-ext (λ _ → cong₂ (λ k c → k c) (valid-K eq-k η) (valid-V eq-v η)) 
    valid-K (user-with-cong eq-m eq-k) η = fun-ext (λ _ → cong₂ bind-tree (cong₂ (λ f c x → f x c) (fun-ext (λ x → valid-K eq-k (η , x) ))  refl) (valid-U eq-m η))  
         
    valid-K (funK-beta k v) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-return v k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-op op p param k l) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-getenv k l) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-setenv c k l) η = refl 
    valid-K (match-with-beta-prod v w k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (user-with-beta-return v k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (user-with-beta-op op p param m k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-eta-K l) η = fun-ext (λ x → cong₂ (λ x₁ x₂ → x₁ x₂) refl refl) 
        --Eq.cong-app refl (⟦ l ⟧-kernel η _) 
    {-(λ C₁ →
         bind-tree (λ { (x , C') → leaf (x , C') }) (⟦ l ⟧-kernel η C₁))
      ≡ ⟦ l ⟧-kernel η-}
    valid-K (GetSetenv _ v) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (SetGetenv c k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (SetSetenv c c' k) η = fun-ext (λ c'' → refl)
    valid-K (GetOpEnv op p param k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (SetOpEnv op p param _) η = {!  !} --Relies on substitution (complete mystery for now)
           
      -}        