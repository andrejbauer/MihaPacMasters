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

trans' : ∀ {A : Set} {x y z : A}
    → x ≡ y 
    → y ≡ z
    -------
    → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z = 
    start 
    x 
    ≡⟨ x≡y ⟩ 
    y 
    ≡⟨ y≡z ⟩ 
    z 
    ∎
    
function-validity : ∀ {A B : Set} {f g : A → B} {x y : A} 
    → f ≡ g 
    → x ≡ y 
    -------------
    → f x ≡ g y
function-validity {_} {_} {f} {g} {x} {y} f≡g x≡y = 
    start 
    (f x 
    ≡⟨ cong f x≡y ⟩ 
    (f y)
    ≡⟨ Eq.cong-app f≡g y ⟩ 
    (g y) 
    ∎)

function4-validity : ∀ {f g a b c d a' b' c' d'}
    → f ≡ g
    → a ≡ a'
    → b ≡ b'
    → c ≡ c'
    → d ≡ d'
    -------------
    → f a b c d ≡ g a' b' c' d'
function4-validity {f} {g} {a} {b} {c} {d} {a'} {b'} {c'} {d'} eq-f eq-a eq-b eq-c eq-d = 
    start 
    (f a b c d 
    ≡⟨ Eq.cong-app eq-f (a b c d) ⟩ 
    (g a b c d 
    ≡⟨ {!   !} ⟩ 
    {!   !})) 


cartesian-validity : ∀ {x x' y y'}
    → x ≡ x'
    → y ≡ y'
    -------------
    → (x , y) ≡ (x' , y')
cartesian-validity eq-x eq-y = {!   !}

proj₁-validity : ∀ {x y}
    → x ≡ y
    --------
    → proj₁ x ≡ proj₁ y
proj₁-validity = {!   !}

proj₂-validity : ∀ {x y}
    → x ≡ y
    -------------------
    → proj₂ x ≡ proj₂ y
proj₂-validity {x} {y} eq = 
    start 
    (x
    ≡⟨ refl ⟩ 
    (proj₁ x , proj₂ x) 
    ≡⟨ eq ⟩ 
    y 
    ≡⟨ {!   !} ⟩ 
    {!   !} )


    --⟦ m₁ ⟧-user ((η , proj₁ (⟦ v₁ ⟧-value η)) , proj₂ (⟦ v₁ ⟧-value η))
match-validity : ∀ {A B X Y : Set} {f g : (A × X) × Y → B} {η : A} {v v' : X × Y}
    → f ≡ g
    → v ≡ v'
    ----------
    → f ((η , proj₁ v) , proj₂ v) ≡ g ((η , proj₁ v') , proj₂ v')

match-validity {_} {_} {_} {_} {f} {g} {η} {v} {v'} eq-f eq-v = 
    function-validity eq-f {! cartesian-validity (cartesian-validity ? (proj₁-validity eq-v)) ?  !}

mutual
-- Naming scheme for the various equalities:
--   Γ ⊢V v ≡ w will be named eq-v, eq-w, ...
--   Γ ⊢U m ≡ n will be named eq-m, eq-n, ...
--   Γ ⊢K k ≡ l will be named eq-k, eq-l, ...
-- This naming scheme will be to quickly show the type of equivalence.

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
    valid-V funU-eta η = fun-ext (λ x → valid-U refl η)
    valid-V funK-eta η = fun-ext (λ x → valid-K refl η)



    valid-U refl η = Eq.refl
    valid-U (sym eq-m) η = Eq.sym (valid-U eq-m η) 
    valid-U (trans eq-m eq-n) η = Eq.trans (valid-U eq-m η) (valid-U eq-n η) 
    valid-U (return-cong eq-v) η = Eq.cong (λ x → leaf x) (valid-V eq-v η)
    valid-U {Γ} {Xᵤ} {m} {n} (·-cong eq-v eq-w) η = function-validity (valid-V eq-v η) (valid-V eq-w η)
        --⟦ v₁ ⟧-value η (⟦ w₁ ⟧-value η) ≡ ⟦ v₂ ⟧-value η (⟦ w₂ ⟧-value η)
        --cong (⟦ _ ⟧-value η) (valid-V eq-w η) 
        --Eq.cong-app (fun-ext (λ x → cong Terms._·_ (valid-V eq-v η) )) (valid-V eq-w η)
    valid-U (opᵤ-cong p eq-v eq-m) η = cong₂ (node _ p) (valid-V eq-v η) (fun-ext (λ res → valid-U eq-m (η , res))) 
    valid-U (let-in-cong eq-m eq-n) η = cong₂ bind-user (fun-ext (λ x → valid-U eq-n (η , x))) (valid-U eq-m η)
    valid-U (match-with-cong eq-v eq-m) η = match-validity {! valid-U eq-m ?  !} (valid-V eq-v η) --Similar to the ·-cong
        --⟦ m₁ ⟧-user ((η , proj₁ (⟦ v₁ ⟧-value η)) , proj₂ (⟦ v₁ ⟧-value η))
        -- ≡
        --⟦ m₂ ⟧-user ((η , proj₁ (⟦ v₂ ⟧-value η)) , proj₂ (⟦ v₂ ⟧-value η))
    valid-U (using-at-run-finally-cong eq-v eq-w eq-m eq-n) η = 
        cong₂ (λ ostalo eta → ⟦ ostalo ⟧-user eta) 
        (cong Terms.`using {!   !} at {!   !} `run {!   !} finally {!   !}) 
        refl 
        --cong₂ bind-tree (fun-ext λ x → {!   !}) {!  !}
        --⟦ `using v₁ at w₁ `run m₁ finally n₁ ⟧-user η ≡
        --⟦ `using v₂ at w₂ `run m₂ finally n₂ ⟧-user η
    valid-U (kernel-at-finally-cong eq-v eq-m eq-k) η = {!   !} --Similar to the ·-cong
        --cong₂ bind-tree (fun-ext (λ {x → valid-U eq-m ((η , {!   !}) !, {!   !}  )})) {! cong   !}
        --{! cong₂ bind-tree (fun-ext (λ x → valid-U eq-m (η , ?) , ?)) ? !}
    valid-U (funU-beta m v) η = {!  !}
    valid-U (let-in-beta-return_ v m) η = {!  !}
    valid-U (let-in-beta-op op p param m n) η = {!   !}
        {- start 
        ({!   !} 
        ≡⟨ {!   !} ⟩ 
        {!   !})
         -}
        --cong₂ (node op p) refl (fun-ext (λ x → cong₂ bind-user (fun-ext (λ x → valid-U {! n  !} {!   !} )) refl))
            {- bind-tree (λ X₁ → ⟦ n ⟧-user (η , X₁)) (⟦ m ⟧-user (η , x)) ≡
            bind-tree
            (λ X₁ →
                ⟦
                (G Substitution.[ O ]ᵤ) n
                (Substitution.extendₛ G O (λ p₁ → var (there p₁)))
                ⟧-user
                ((η , x) , X₁))
            (⟦ m ⟧-user (η , x))-}
    valid-U (match-with-beta-prod v w m) η = {!  !}
    valid-U (using-run-finally-beta-return r w v m) η = {!  !}
    valid-U (using-run-finally-beta-op R w op param p m n) η = {!  !}
    valid-U (kernel-at-finally-beta-return v c n) η = {!  !}
    valid-U (kernel-at-finally-beta-getenv c k m) η = {!  !}
    valid-U (kernel-at-finally-setenv c c' k m) η = cong₂ bind-user refl refl
    valid-U (kernel-at-finally-beta-op op p param c k m) η = {!  !}
    valid-U (let-in-eta-M n) η = Eq.cong-app refl (⟦ n ⟧-user η) 

    valid-K refl η = Eq.refl
    valid-K (sym eq-k) η = Eq.sym (valid-K eq-k η)
    valid-K (trans eq-k eq-l) η = Eq.trans (valid-K eq-k η) (valid-K eq-l η) 
    valid-K (return-cong eq-v) η = fun-ext (λ x → cong leaf {!       !}) 
    valid-K (·-cong eq-v eq-w) η = {!   !}
    valid-K (let-in-cong eq-k eq-l) η = {!   !}
        --fun-ext λ c → (cong₂ bind-tree (fun-ext (λ x → {!  valid-K eq-l (( η , proj₁ x ) , proj₂ x)    !})) {!   !})    --(λ x → cong₂ bind-tree {!   !} {!   !})
    valid-K (match-with-cong eq-v eq-k) η = {!   !}
    valid-K (opₖ-cong eq-v eq-k) η = {!  !}
    valid-K (getenv-cong eq-k) η = {!   !}
    valid-K (setenv-cong eq-v eq-k) η = {!  !}
    valid-K (user-with-cong eq-m eq-k) η = {!   !}
    valid-K (funK-beta k v) η = {!  !}
    valid-K (let-in-beta-return v k) η = {!  !}
    valid-K (let-in-beta-op op p param k l) η = {!  !}
    valid-K (let-in-beta-getenv k l) η = {!  !}
    valid-K (let-in-beta-setenv c k l) η = {!  !}
    valid-K (match-with-beta-prod v w k) η = {!  !}
    valid-K (user-with-beta-return v k) η = {!  !}
    valid-K (user-with-beta-op op p param m k) η = {!  !}
    valid-K (let-in-eta-K _) η = {!  !}
    valid-K (GetSetenv _ v) η = {!  !}
    valid-K (SetGetenv c k) η = {!  !}
    valid-K (SetSetenv c c' k) η = fun-ext (λ c'' → refl)
    valid-K (GetOpEnv op p param k) η = {!  !}
    valid-K (SetOpEnv op p param _) η = {!  !}
 