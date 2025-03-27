--{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning     -- using ( _≡⟨⟩_ ; _∎ ) renaming (begin_ to start_ ; step-≡ to step-= ) 
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
import Sub-Validity

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
open Sub-Validity G O
 
tree-id-lemma : ∀ {X Σ} (t : Tree Σ ⟦ X ⟧v)
    → bind-tree leaf t ≡ t
tree-id-lemma {X} {Σ} (leaf x) = refl
tree-id-lemma {X} {Σ} (node op p param t) = cong (node op p param) 
    (fun-ext (λ res → tree-id-lemma {X = X} {Σ = Σ} (t res)))

mutual

    valid-V : ∀ {Γ : Ctx} {X : VType} {v w : Γ ⊢V: X} → (Γ ⊢V v ≡ w) → ∀ η → ⟦ v ⟧-value η ≡ ⟦ w ⟧-value η
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
    valid-V {w = w} funU-eta η = fun-ext (λ x → 
        cong₂ (λ a b → a b) 
            {x = ⟦ w [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , x)}
            {y = ⟦ w ⟧-value η}
            {u = x}
            {v = x}
            (Eq.sym (Eq.trans 
                (cong ⟦ w ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (sub-ren-value w wkᵣ (η , x))))
            refl)
    valid-V {w = w} funK-eta η = fun-ext (λ X → 
        cong₂ (λ a b → a b) 
            {x = ⟦ w [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , X)}
            {y = ⟦ w ⟧-value η}
            (Eq.sym (Eq.trans
                (cong ⟦ w ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (sub-ren-value w wkᵣ (η , X))))
            refl)




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
    valid-U (funU-beta m v) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ sub-var refl)) (sub-U (var ∷ₛ v) η m)
    valid-U (let-in-beta-return_ v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ sub-var refl)) (sub-U (var ∷ₛ v) η m)
    valid-U (let-in-beta-op op p param m n) η = cong (node op p (⟦ param ⟧-value η)) 
        (fun-ext (λ res → 
            cong₂ bind-tree 
                {x = (λ X₁ → ⟦ n ⟧-user (η , X₁))}
                {y = (λ X₁ → ⟦ n [ extendₛ (λ x → var (there x)) ]ᵤ ⟧-user ((η , res) , X₁))}
                {u = (⟦ m ⟧-user (η , res))}
                {v = (⟦ m ⟧-user (η , res))}
                (fun-ext (λ X₁ → Eq.trans
                        (cong ⟦ n ⟧-user (cong (_, X₁)
                            (begin 
                            η 
                            ≡⟨ sub-id-lemma η ⟩ 
                            ⟦ var ⟧-sub η 
                            ≡⟨ sub-wk var η ⟩ 
                            ⟦ (λ x → var x [ there {X = {!   !}} ]ᵥᵣ) ⟧-sub (η , res)
                            ≡⟨ sub-wk (λ x → var x [ there {X = {!   !}} ]ᵥᵣ) (η , res) ⟩ 
                            (⟦ (λ x → var (wkᵣ (there x))) ⟧-sub ((η , res) , X₁)) 
                            ≡⟨⟩ 
                            refl
                            )
                        (sub-U (extendₛ (λ x₁ → var (there x₁))) ((η , res) , X₁) n))) 
                refl
            ))
    valid-U (match-with-beta-prod v w m) η = Eq.trans 
        (cong ⟦ m ⟧-user (cong (_, ⟦ w ⟧-value η) (cong (_, ⟦ v ⟧-value η) (sub-id-lemma η)))) 
        (sub-U ((var ∷ₛ v) ∷ₛ w) η m)
    valid-U (using-run-finally-beta-return r w v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (cong₂ _,_ sub-var refl) refl))
        (sub-U ((var ∷ₛ v) ∷ₛ w) η m)
    valid-U (using-run-finally-beta-op R w op param p m n) η = {! cong₂ bind-tree 
        {x = (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c') })}
        (fun-ext (λ { x → ? })) 
        (cong₂ bind-tree 
            ? 
            (Eq.trans 
                ? 
                (sub-U ? ? ?))) !}

    --{! cong₂ bind-tree ? (cong₂ bind-tree ? (Eq.trans ? (sub-U )))   !} 
    valid-U (kernel-at-finally-beta-return v c n) η = Eq.trans 
        (cong ⟦ n ⟧-user (cong (λ a → (a , ⟦ v ⟧-value η) , ⟦ c ⟧-value η) (sub-id-lemma η))) 
        (sub-U ((var ∷ₛ v) ∷ₛ c) η n) 
    valid-U (kernel-at-finally-beta-getenv c k m) η = cong₂ bind-tree
        {x = (λ { (X , C) → ⟦ m ⟧-user ((η , X) , C) })}
        {y = (λ { (X , C) → ⟦ m ⟧-user ((η , X) , C) })}
        {u = (⟦ k ⟧-kernel (η , ⟦ c ⟧-value η) (⟦ c ⟧-value η))}
        {v = (⟦ k [ var ∷ₛ c ]ₖ ⟧-kernel η (⟦ c ⟧-value η))}
        (fun-ext (λ (X , C) → refl))
        (cong (λ a → a (⟦ c ⟧-value η)) 
            {x = ⟦ k ⟧-kernel (η , ⟦ c ⟧-value η)} 
            {y = ⟦ k [ var ∷ₛ c ]ₖ ⟧-kernel η}
            (Eq.trans
                (cong ⟦ k ⟧-kernel (cong (_, ⟦ c ⟧-value η) (sub-id-lemma η)))
                (sub-K (var ∷ₛ c) η k)))
    valid-U (kernel-at-finally-setenv c c' k m) η = refl --Strange
    valid-U (kernel-at-finally-beta-op op p param c k m) η = cong (node op p (⟦ param ⟧-value η)) 
        (fun-ext (λ res → 
            cong₂ bind-tree 
                {x = (λ { (X , C) → ⟦ m ⟧-user ((η , X) , C) })}
                {y = (λ { (X , C) → ⟦ m [ extendₛ (extendₛ (λ x → var (there x))) ]ᵤ ⟧-user (((η , res) , X) , C) })}
                {u = (⟦ k ⟧-kernel (η , res) (⟦ c ⟧-value η))}
                {v = (⟦ k ⟧-kernel (η , res) (⟦ c [ (λ x → var (there x)) ]ᵥ ⟧-value (η , res)))}
                (fun-ext (λ (X , C) → 
                    begin 
                    ⟦ m ⟧-user ((η , X) , C) 
                    ≡⟨ cong ⟦ m ⟧-user (cong (λ a → (a , X) , C) 
                        (begin 
                        η 
                        ≡⟨ sub-id-lemma η ⟩
                        ⟦ var ⟧-sub η
                        ≡⟨ sub-wk var η ⟩  
                        ⟦ (λ x → var (there x)) ⟧-sub (η , res)
                        ≡⟨ sub-wk (λ x → var (there x)) (η , res) ⟩
                        ⟦ (λ x → var (there (there x))) ⟧-sub ((η , res) , X)
                        ≡⟨ sub-wk (λ x → var (there (there x))) ((η , res) , X) ⟩
                        ⟦ (λ x → var (there {X = {!   !}} (there {X = {!   !}} (there x)))) ⟧-sub (((η , res) , X) , C) 
                        ∎
                        )) ⟩ 
                    ⟦ m ⟧-user (⟦ extendₛ (extendₛ (λ x → var (there x))) ⟧-sub (((η , res) , X) , C)) 
                    ≡⟨ sub-U (extendₛ (extendₛ (λ x → var (there x)))) (((η , res) , X) , C)  m ⟩ 
                    ⟦ m [ extendₛ (extendₛ (λ x → var (there x))) ]ᵤ ⟧-user (((η , res) , X) , C) 
                    ∎
                ))
                (cong (⟦ k ⟧-kernel (η , res)) (Eq.trans
                    (cong ⟦ c ⟧-value (Eq.trans
                        (sub-id-lemma η)
                        (sub-wk idₛ η)))
                    (sub-V (λ x → var (there x)) (η , res) c))))) 
    valid-U (let-in-eta-M n) η = begin
        bind-tree (λ X₁ → leaf X₁) (⟦ n ⟧-user η)
        ≡⟨ (Eq.cong-app {f = bind-tree (λ X₁ → leaf X₁) } {g = bind-tree leaf} refl (⟦ n ⟧-user η)) ⟩
        bind-tree leaf (⟦ n ⟧-user η)
        ≡⟨ tree-id-lemma {X = {!   !}} {Σ = {!   !}} (⟦ n ⟧-user η) ⟩
        ⟦ n ⟧-user η
        ∎
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
    valid-K (funK-beta k v) η = Eq.trans 
        (cong ⟦ k ⟧-kernel (cong (_, ⟦ v ⟧-value η) (sub-id-lemma η)))
        (sub-K (var ∷ₛ v) η k) 
    valid-K (let-in-beta-return v k) η = fun-ext (λ C → cong (λ a → a C) (valid-K (funK-beta k v) η)) 
    valid-K (let-in-beta-op op p param k l) η = fun-ext (λ C → 
        cong (node op p (⟦ param ⟧-value η)) 
        (fun-ext (λ res → cong (λ a → bind-tree a (⟦ k ⟧-kernel (η , res) C)) 
            (fun-ext (λ (x , C') → cong (λ a → a C') 
                {x = ⟦ l ⟧-kernel (η , x)}
                {y = ⟦ l [ extendₛ (λ x₁ → var (there x₁)) ]ₖ ⟧-kernel ((η , res) , x)}
                (begin 
                (⟦ l ⟧-kernel (η , x) 
                ≡⟨ cong ⟦ l ⟧-kernel (cong (_, x) 
                    (begin
                    η 
                    ≡⟨ sub-id-lemma η ⟩
                    ⟦ var ⟧-sub η
                    ≡⟨ sub-wk var η ⟩
                    ⟦ (λ x₁ → var x₁ [ there ]ᵥᵣ) ⟧-sub (η , res)
                    ≡⟨ sub-wk (λ x₁ → var x₁ [ there ]ᵥᵣ) (η , res) ⟩ 
                    ⟦ (λ x₁ → var (there (there x₁))) ⟧-sub ((η , res) , x)
                    ∎
                    )) ⟩ 
                ⟦ l ⟧-kernel
                  (⟦ extendₛ {X = {!   !}} (λ x₁ → var (there x₁)) ⟧-sub ((η , res) , x))
                ≡⟨ sub-K (extendₛ (λ x₁ → var (there x₁))) ((η , res) , x) l ⟩ 
                ⟦ l [ extendₛ (λ x₁ → var (there x₁)) ]ₖ ⟧-kernel ((η , res) , x) 
                ∎
                ))))))
        ) 
    valid-K (let-in-beta-getenv k l) η = fun-ext (λ C → 
        cong (λ a → bind-tree a (⟦ k ⟧-kernel (η , C) C)) 
            (fun-ext (λ (x , C') → 
                cong (λ a → a C')
                    {x = ⟦ l ⟧-kernel (η , x)}
                    {y = ⟦ l [ extendₛ (λ x₁ → var (there x₁)) ]ₖ ⟧-kernel ((η , C) , x)}
                    ((begin 
                (⟦ l ⟧-kernel (η , x) 
                ≡⟨ cong ⟦ l ⟧-kernel (cong (_, x) 
                    (begin
                    η 
                    ≡⟨ sub-id-lemma η ⟩
                    ⟦ var ⟧-sub η
                    ≡⟨ sub-wk var η ⟩
                    ⟦ (λ x₁ → var x₁ [ there ]ᵥᵣ) ⟧-sub (η , C)
                    ≡⟨ sub-wk (λ x₁ → var x₁ [ there ]ᵥᵣ) (η , C) ⟩ 
                    ⟦ (λ x₁ → var (there (there x₁))) ⟧-sub ((η , C) , x)
                    ∎
                    )) ⟩ 
                    ⟦ l ⟧-kernel
                    (⟦ extendₛ {X = {!   !}} (λ x₁ → var (there x₁)) ⟧-sub ((η , C) , x))
                    ≡⟨ sub-K (extendₛ (λ x₁ → var (there x₁))) ((η , C) , x) l ⟩ 
                    ⟦ l [ extendₛ (λ x₁ → var (there x₁)) ]ₖ ⟧-kernel ((η , C) , x) 
                    ∎
                    )))))) 
    valid-K (let-in-beta-setenv c k l) η = refl 
    valid-K (match-with-beta-prod v w k) η = Eq.trans
        (cong (λ a → ⟦ k ⟧-kernel ((a , ⟦ v ⟧-value η) , ⟦ w ⟧-value η)) (sub-id-lemma η))
        (sub-K ((var ∷ₛ v) ∷ₛ w) η k) 
    valid-K (user-with-beta-return v k) η = fun-ext (λ C → 
        cong (λ a → a C) 
            {x = ⟦ k ⟧-kernel (η , ⟦ v ⟧-value η)}
            {y = ⟦ k [ var ∷ₛ v ]ₖ ⟧-kernel η}
            (Eq.trans 
                (cong (λ a → ⟦ k ⟧-kernel (a , ⟦ v ⟧-value η)) 
                    (sub-id-lemma η))
                (sub-K (var ∷ₛ v) η k))) 
    valid-K (user-with-beta-op op p param m k) η = fun-ext (λ C → 
        cong (node op p (⟦ param ⟧-value η)) (fun-ext (λ res → 
            cong (λ a → bind-tree a (⟦ m ⟧-user (η , res))) 
                (fun-ext (λ X → cong (λ a → a C) 
                    {x = ⟦ k ⟧-kernel (η , X)}
                    {y = ⟦ k [ extendₛ (λ x → var (there x)) ]ₖ ⟧-kernel ((η , res) , X)}
                    (Eq.trans
                        (cong ⟦ k ⟧-kernel (cong (_, X) 
                            (begin
                            η
                            ≡⟨ sub-id-lemma η ⟩
                            ⟦ var ⟧-sub η
                            ≡⟨ sub-wk var η ⟩
                            ⟦ (λ x → var (there x)) ⟧-sub (η , res)
                            ≡⟨ sub-wk (λ x → var (there x)) (η , res) ⟩ 
                            ⟦ (λ x → var (there (there x))) ⟧-sub ((η , res) , X)
                            ∎)))
                        (sub-K (extendₛ (λ x → var (there x))) ((η , res) , X) k))))))) 
    valid-K (let-in-eta-K l) η = fun-ext (λ x → begin
        bind-tree (λ { (x , C') → leaf (x , C') }) (⟦ l ⟧-kernel η x)
        ≡⟨ (Eq.cong-app {f = bind-tree (λ { (x , C') → leaf (x , C') }) } 
            {g = bind-tree leaf} refl (⟦ l ⟧-kernel η x)) ⟩
        bind-tree leaf ((⟦ l ⟧-kernel η x))
        ≡⟨ tree-id-lemma {X = {!   !}} {Σ = {!   !}} ((⟦ l ⟧-kernel η x)) ⟩
        ⟦ l ⟧-kernel η x
        ∎) 
    valid-K (GetSetenv _ v) η = {!   !}
    valid-K (SetGetenv c k) η = fun-ext (λ _ → 
        cong (λ a → a (⟦ c ⟧-value η))
            {x = ⟦ k ⟧-kernel (η , ⟦ c ⟧-value η)}
            {y = ⟦ k [ var ∷ₛ c ]ₖ ⟧-kernel η}
            (Eq.trans 
                (cong ⟦ k ⟧-kernel (cong (_, ⟦ c ⟧-value η) (sub-id-lemma η)))
                (sub-K (var ∷ₛ c) η k))) 
    valid-K (SetSetenv c c' k) η = fun-ext (λ c'' → refl)
    valid-K (GetOpEnv op p param k) η = fun-ext (λ C → 
        cong₂ (node op p) 
            (Eq.sym (Eq.trans 
                (cong ⟦ param ⟧-value (Eq.trans
                    (sub-id-lemma η)
                    (sub-wk var η)))
                (sub-V (λ x → var (there x)) (η , C) param))) 
            (fun-ext (λ res → cong (λ a → a C) 
                {x = ⟦ k [ (λ x → var (there (there x))) ]ₖ ⟧-kernel ((η , C) , res)}
                {y = ⟦ k [ (λ x → var (there (there x))) ]ₖ ⟧-kernel ((η , res) , C)}
                (begin 
                ⟦ k [ (λ x → var (there (there x))) ]ₖ ⟧-kernel ((η , C) , res)
                ≡⟨ Eq.sym (sub-K (λ x → var (there (there x))) ((η , C) , res) k) ⟩
                ⟦ k ⟧-kernel
                  (⟦ (λ x → var (there (there x))) ⟧-sub ((η , C) , res))
                ≡⟨ cong ⟦ k ⟧-kernel (Eq.sym (Eq.trans
                    (sub-id-lemma η)
                    (Eq.trans
                        (sub-wk var η)
                        (sub-wk (λ x → var (there x)) (η , C))))) ⟩
                ⟦ k ⟧-kernel η
                ≡⟨ cong ⟦ k ⟧-kernel (Eq.trans
                    (sub-id-lemma η)
                    (Eq.trans
                        (sub-wk var η)
                        (sub-wk (λ x → var (there x)) (η , res)))) ⟩
                ⟦ k ⟧-kernel
                  (⟦ (λ x → var (there (there x))) ⟧-sub ((η , res) , C))
                ≡⟨ sub-K (λ x → var (there (there x))) ((η , res) , C) k ⟩
                ⟦ k [ (λ x → var (there (there x))) ]ₖ ⟧-kernel ((η , res) , C)
                ∎
                )
                ))
            ) 
    valid-K (SetOpEnv op p param _) η = fun-ext (λ _ → 
        {!   !}) 