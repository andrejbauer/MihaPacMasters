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
open import Ren-Validity G O

sub-coop-lemma : ∀ { Γ Γ' Σ C op } (σ : Sub Γ Γ') (coop : co-op Γ' Σ C op)
    → coop [ extendₛ σ ]ₖ  ≡ sub-coop coop σ
sub-coop-lemma σ (sub-kernel coop x) = refl
sub-coop-lemma σ (return x) = refl
sub-coop-lemma σ (x · x₁) = refl
sub-coop-lemma σ (`let coop `in coop₁) = refl
sub-coop-lemma σ (match x `with coop) = refl
sub-coop-lemma σ (opₖ op x x₁ coop) = refl
sub-coop-lemma σ (getenv coop) = refl
sub-coop-lemma σ (setenv x coop) = refl
sub-coop-lemma σ (user x `with coop) = refl


mutual
-- Naming scheme for the various equalities:
--   Γ ⊢V v ≡ w will be named eq-v, eq-w, ...
--   Γ ⊢U m ≡ n will be named eq-m, eq-n, ...
--   Γ ⊢K k ≡ l will be named eq-k, eq-l, ...
-- This naming scheme will be to quickly show the type of equivalence.

    ⟦_⟧-sub : ∀ {Γ Γ'} → Sub Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx  
    ⟦_⟧-sub {Γ' = []} σ η = tt
    ⟦_⟧-sub {Γ' = Γ' ∷ X} σ η = (⟦ σ ∘ there ⟧-sub η) , ⟦ σ here ⟧-value η
        
    sub-wk : ∀ {Γ Γ' X} {v : ⟦ X ⟧v} (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ (λ y → there {Y = X} y) ]ᵥᵣ) ⟧-sub (η , v)
    sub-wk {Γ} {[]} σ η = refl
    sub-wk {Γ} {Γ' ∷ X'} {v = v} σ η = cong₂ _,_ 
        (sub-wk (σ ₛ∘ᵣ there) η)
        (begin 
        ⟦ σ here ⟧-value η 
        ≡⟨ cong ⟦ σ here ⟧-value (Eq.trans (ren-id-lemma η) (ren-wk idᵣ η)) ⟩ 
        ⟦ σ here ⟧-value (⟦ there ⟧-ren (η , v))
        ≡⟨ ren-value (σ here) there (η , _) ⟩ 
        refl)

    sub-id-lemma : ∀ { Γ } (η : ⟦ Γ ⟧-ctx)
        → η ≡ ⟦ (λ x → var x) ⟧-sub η
    sub-id-lemma {Contexts.[]} η = refl
    sub-id-lemma {Γ Contexts.∷ X} (η , v) = cong (_, v) 
        (begin 
        η 
        ≡⟨ sub-id-lemma η ⟩ 
        ⟦ idₛ ⟧-sub η 
        ≡⟨ sub-wk idₛ η ⟩ 
        ⟦ (λ x → var (there x)) ⟧-sub (η , v) 
        ∎)

    sub-V : ∀ { Γ Γ' X  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (v : Γ' ⊢V: X)
        → ⟦ v ⟧-value (⟦ σ ⟧-sub η) ≡ ⟦ v [ σ ]ᵥ ⟧-value η
    sub-V {Γ' = Γ' ∷ X} σ η (var here) = refl
    sub-V {Γ' = Γ' ∷ X} σ η (var (there x)) = sub-V {Γ' = Γ'} (σ ∘ (there {Y = X})) η (var x)
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
    sub-V {Γ} {Γ'} {Σ ⇒ Σ' , C'} σ η (runner {Σ} {Σ'} {C'} r) = fun-ext (λ op → fun-ext (λ x → fun-ext (λ par → 
        begin 
        ⟦ r op x ⟧-kernel (⟦ σ ⟧-sub η , par) 
        ≡⟨ cong ⟦ r op x ⟧-kernel (cong₂ _,_ (sub-wk σ η) refl) ⟩ 
        ⟦ r op x ⟧-kernel (⟦ (λ x₁ → σ x₁ [ there ]ᵥᵣ) ⟧-sub (η , par) , par)
        ≡⟨ refl ⟩
        ⟦ r op x ⟧-kernel (⟦ extendₛ {X = gnd (param op)} σ ⟧-sub (η , par)) 
        ≡⟨ sub-K (extendₛ σ) (η , par) (r op x) ⟩ 
        ⟦ r op x [ extendₛ σ ]ₖ ⟧-kernel (η , par)
        ≡⟨ cong (λ a → ⟦ a ⟧-kernel (η , par)) {y = sub-coop (r op x) σ} (sub-coop-lemma σ (r op x)) ⟩ 
        ⟦ sub-coop (r op x) σ ⟧-kernel (η , par)
        ≡⟨ refl ⟩
        refl
        )))
    --POTENTIAL TODO 11. 3.: use begin_ syntactic sugar to make the proofs prettier. 

    sub-U : ∀ { Γ Γ' Xᵤ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (m : Γ' ⊢U: Xᵤ)
        → ⟦ m ⟧-user (⟦ σ ⟧-sub η) ≡ ⟦ m [ σ ]ᵤ ⟧-user η
    sub-U σ η (sub-user m p) = cong (coerceᵤ p) (sub-U σ η m)
    sub-U σ η (return v) = cong leaf (sub-V σ η v) 
    sub-U σ η (v · w) = cong₂ (λ a b → a b) (sub-V σ η v) (sub-V σ η w)
    sub-U {Γ} {Γ'} {X ! Σ} σ η (opᵤ {X'} op p par m) = cong₂ (node op p) (sub-V σ η par) (fun-ext (λ res → 
        (begin
        ⟦ m ⟧-user (⟦ σ ⟧-sub η , res)
        ≡⟨    (cong ⟦ m ⟧-user (cong₂ _,_ 
                (sub-wk σ η) 
                refl)) ⟩
        ⟦ m ⟧-user (⟦ extendₛ {Γ} {Γ'} {gnd (result op)} σ ⟧-sub (η , res))
        ≡⟨    (sub-U (extendₛ σ) (η , res) m)⟩
        ⟦ m [ extendₛ σ ]ᵤ ⟧-user (η , res)
        ∎)))
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
                ≡⟨ cong ⟦ n ⟧-user (cong₂ _,_ 
                    (cong₂ _,_ 
                        (Eq.trans
                            (sub-wk σ η)
                            (sub-wk (wkₛ σ) (η , x)))
                        refl)
                    refl) ⟩ 
                ⟦ n ⟧-user ((⟦ (λ x₁ → (σ x₁ [ wkᵣ ]ᵥᵣ) [ wkᵣ ]ᵥᵣ) ⟧-sub ((η , x) , c') , x) , c') 
                ≡⟨ sub-U (extendₛ (extendₛ σ)) ((η , x) , c') n ⟩
                ⟦ n [ extendₛ (extendₛ σ) ]ᵤ ⟧-user ((η , x) , c') 
                ≡⟨ refl ⟩ 
                refl
                ))
            (cong₂ (λ a b → a b)
                {x = apply-runner (⟦ r ⟧-value (⟦ σ ⟧-sub η)) (⟦ m ⟧-user (⟦ σ ⟧-sub η))}
                {y = apply-runner (⟦ r [ σ ]ᵥ ⟧-value η) (⟦ m [ σ ]ᵤ ⟧-user η)}
                (cong₂ apply-runner 
                    {x = ⟦ r ⟧-value (⟦ σ ⟧-sub η)}
                    {y = ⟦ r [ σ ]ᵥ ⟧-value η}
                    {u = ⟦ m ⟧-user (⟦ σ ⟧-sub η)}
                    {v = ⟦ m [ σ ]ᵤ ⟧-user η}
                    (sub-V σ η r)
                    (sub-U σ η m))
                (sub-V σ η c))
    sub-U {Γ} {Γ'} {X' ! Σ} σ η (kernel k at c finally m) = cong₂ bind-tree
        {x = (λ { (X , C) → ⟦ m ⟧-user ((⟦ σ ⟧-sub η , X) , C) })}
        {y = (λ { (X , C) → ⟦ m [ extendₛ (extendₛ σ) ]ᵤ ⟧-user ((η , X) , C) })}
        {u = (⟦ k ⟧-kernel (⟦ σ ⟧-sub η) (⟦ c ⟧-value (⟦ σ ⟧-sub η)))}
        {v = (⟦ k [ σ ]ₖ ⟧-kernel η (⟦ c [ σ ]ᵥ ⟧-value η))}
            (fun-ext (λ (X , C) → Eq.trans 
                (cong ⟦ m ⟧-user (cong₂ _,_ 
                    (cong₂ _,_ 
                        (begin 
                        (⟦ σ ⟧-sub η 
                        ≡⟨ sub-wk σ η ⟩ 
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
                (Eq.trans
                    (cong ⟦ l ⟧-kernel (cong₂ _,_
                        (sub-wk σ η)
                        refl))
                    (sub-K (extendₛ σ) (η , X) l))
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
    sub-K σ η (setenv c k) = fun-ext (λ C → 
        cong₂ (λ a b → a b) 
            {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η)}  
            {y = ⟦ k [ σ ]ₖ ⟧-kernel η} 
            {u = (⟦ c ⟧-value (⟦ σ ⟧-sub η))} 
            {v = (⟦ c [ σ ]ᵥ ⟧-value η)}
            (fun-ext (λ _ → cong₂ (λ a b → a b)
                {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η)}
                {y = ⟦ k [ σ ]ₖ ⟧-kernel η}
                (sub-K σ η k)
                refl))
            (sub-V σ η c))
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
                      
                                 