{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function

import Contexts
open import Parameters
import Types
import Terms
import Monads
import Equations

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

  -- Denotation of a runner
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

  apply-runner : ∀ {Σ Σ' C X} → Runner Σ Σ' C → UComp Σ X → KComp Σ' C X
  apply-runner R (leaf x) c = leaf (x , c)
  apply-runner R (node op p param κ) = bind-kernel (apply-runner R ∘ κ) (R op p param)

  kernel-to-user : ∀ {Σ X Y C} → KComp Σ C X → C → (X × C → UComp Σ Y) → UComp Σ Y
  kernel-to-user k c m = bind-user m (k c)

  ⟦_⟧-user : ∀ {Γ Xᵤ} → (Γ ⊢U: Xᵤ) → ⟦ Γ ⟧-ctx → ⟦ Xᵤ ⟧u
  ⟦ sub-user m p ⟧-user η = coerceᵤ p (⟦ m ⟧-user η)
  ⟦ return v ⟧-user η = leaf (⟦ v ⟧-value η)
  ⟦ v · w ⟧-user η = ⟦ v ⟧-value η (⟦ w ⟧-value η)
  ⟦ opᵤ op p v m ⟧-user η = node op p (⟦ v ⟧-value η) λ res → ⟦ m ⟧-user (η , res)
  ⟦ `let m `in n ⟧-user η = bind-user (λ X → ⟦ n ⟧-user (η , X)) (⟦ m ⟧-user η)
  ⟦ match v `with m ⟧-user η = ⟦ m ⟧-user ((η , (proj₁ (⟦ v ⟧-value η))) , (proj₂ (⟦ v ⟧-value η)))
  ⟦ `using r at c `run m finally n ⟧-user η =
     kernel-to-user (apply-runner (⟦ r ⟧-value η) (⟦ m ⟧-user η)) (⟦ c ⟧-value η) (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c')})

  ⟦ kernel k at c finally m ⟧-user η = kernel-to-user  (⟦ k ⟧-kernel η) (⟦ c ⟧-value η) (λ {(X , C) → ⟦ m ⟧-user ((η , X) , C)})

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

-- Validity of equations
module _ where

  open Equations G O

  mutual

    valid-V : ∀ {Γ : Ctx} {X : VType} {v w : Γ ⊢V: X} → (Γ ⊢V v ≡ w) → ∀ η → ⟦ v ⟧-value η ≡ ⟦ w ⟧-value η
    valid-U : ∀ {Γ : Ctx} {Xᵤ : UType} {m n : Γ ⊢U: Xᵤ} → (Γ ⊢U m ≡ n) → ∀ η → ⟦ m ⟧-user η ≡ ⟦ n ⟧-user η
    valid-K : ∀ {Γ : Ctx} {Xₖ : KType} {k l : Γ ⊢K: Xₖ} → (Γ ⊢K k ≡ l) → ∀ η → ⟦ k ⟧-kernel η ≡ ⟦ l ⟧-kernel η

    valid-V refl η = Eq.refl
    valid-V (sym eq) η = Eq.sym (valid-V eq η)
    valid-V (trans eq₁ eq₂) η = Eq.trans (valid-V eq₁ η) (valid-V eq₂ η)
    valid-V (prod-cong eq₁ eq₂) η = Eq.cong₂ _,_ (valid-V eq₁ η) (valid-V eq₂ η)
    valid-V (fun-cong eq) η = fun-ext (λ x → valid-U eq (η , x))
    valid-V (funK-cong x) η = {!!}
    valid-V (runner-cong x) η = {!!}
    valid-V unit-eta η = {!!}
    valid-V funU-eta η = {!!}
    valid-V funK-eta η = {!!}

    valid-U refl η = {!!}
    valid-U (sym eq) η = {!!}
    valid-U (trans eq eq₁) η = {!!}
    valid-U (return-cong x) η = {!!}
    valid-U (·-cong x x₁) η = {!!}
    valid-U (opᵤ-cong p eq₁ eq₂) η = cong₂ (node _ p) (valid-V eq₁ η) (fun-ext (λ x → valid-U eq₂ (η , x)))
    valid-U (let-in-cong eq eq₁) η = {!!}
    valid-U (match-with-cong x eq) η = {!!}
    valid-U (using-at-run-finally-cong x x₁ eq eq₁) η = {!!}
    valid-U (kernel-at-finally-cong x eq x₁) η = {!!}
    valid-U (funU-beta m v) η = {!!}
    valid-U (let-in-beta-return_ v m) η = {!!}
    valid-U (let-in-beta-op op p v m n) η = {!!}
    valid-U (match-with-beta-prod v₁ v₂ m) η = {!!}
    valid-U (using-run-finally-beta-return r w v n) η = {!!}
    valid-U (using-run-finally-beta-op R w op v p m n) η = {!!}
    valid-U (kernel-at-finally-beta-return v w n) η = {!!}
    valid-U (kernel-at-finally-beta-getenv v k m) η = {!!}
    valid-U (kernel-at-finally-setenv v w k m) η = {!!}
    valid-U (kernel-at-finally-beta-op op p v w k m) η = {!!}
    valid-U (let-in-eta-M _) η = {!!}

    valid-K refl η = {!!}
    valid-K (sym eq) η = {!!}
    valid-K (trans eq eq₁) η = {!!}
    valid-K (return-cong x) η = {!!}
    valid-K (·-cong x x₁) η = {!!}
    valid-K (let-in-cong eq eq₁) η = {!!}
    valid-K (match-with-cong x eq) η = {!!}
    valid-K (opₖ-cong x eq) η = {!!}
    valid-K (getenv-cong eq) η = {!!}
    valid-K (setenv-cong x eq) η = {!!}
    valid-K (user-with-cong x eq) η = {!!}
    valid-K (funK-beta k v) η = {!!}
    valid-K (let-in-beta-return v k) η = {!!}
    valid-K (let-in-beta-op op p v k l) η = {!!}
    valid-K (let-in-beta-getenv k l) η = {!!}
    valid-K (let-in-beta-setenv v k l) η = {!!}
    valid-K (match-with-beta-prod v w k) η = {!!}
    valid-K (user-with-beta-return v k) η = {!!}
    valid-K (user-with-beta-op op p v m k) η = {!!}
    valid-K (let-in-eta-K _) η = {!!}
    valid-K (GetSetenv _ v) η = {!!}
    valid-K (SetGetenv v k) η = {!!}
    valid-K (SetSetenv v w k) η = {!!}
    valid-K (GetOpEnv op p v k) η = {!!}
    valid-K (SetOpEnv op p v _) η = {!!}
