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

module Monads (G : GTypes) (O : Ops G) where --TODO: Organize things into separate files (17. 12. 2024)

open import Level        renaming (zero to lzero; suc to lsuc)
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O

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

-- Denotation of ground types
⟦_⟧g : GType → Set
⟦ base b ⟧g =  ⟦ b ⟧b
⟦ unit ⟧g = ⊤
⟦ A ×b B ⟧g = ⟦ A ⟧g × ⟦ B ⟧g

-- A computation tree that hold values of type T in their leaves
data Tree  (Σ : Sig) (X : Set) : Set where
  leaf : X → Tree Σ X
  node : ∀ (op : Op) → (p : op ∈ₒ Σ) → (param : ⟦ param op ⟧g) → (t : (res : ⟦ result op ⟧g) → Tree Σ X) → Tree Σ X

aux : ∀{op Σ₁ Σ₂ } → op ∈ₒ Σ₁ → Σ₁ ⊆ₛ Σ₂ → op ∈ₒ Σ₂ -- auxilliary function for include-tree
aux {op} p q = q op p

include-tree : ∀ {Σ₁ Σ₂ X} → Σ₁ ⊆ₛ Σ₂ → Tree Σ₁ X → Tree Σ₂ X
include-tree p (leaf x) = leaf x
include-tree p (node op q param c) = node op (aux q p) param (λ res → include-tree p (c res))

-- Monadic bind for trees
bind-tree : ∀ {Σ X Y} → (X → Tree Σ Y) → Tree Σ X → Tree Σ Y
bind-tree f (leaf x) = f x
bind-tree f (node op p param c) = node op p param (λ res → bind-tree f (c res))

map-tree : ∀ {Σ X Y} → (X → Y) → Tree Σ X → Tree Σ Y
map-tree f t = bind-tree (leaf ∘ f) t

-- Denotation of a user computation returning elements of X and performing operations Σ
UComp : Sig → Set → Set
UComp Σ X = Tree Σ X --TODO: Prove that THIS/Tree(X) is a Monad, the UComp will be T, bind is the bind-tree, leaf is the unit η,
--when verifying equations keep in mind that you might have to use funext

bind-user : ∀ {Σ X Y} → (X → UComp Σ Y) → UComp Σ X → UComp Σ Y
bind-user = bind-tree

-- Denotation of a kernel computation with state C returning elements of X
KComp : Sig → Set → Set → Set
KComp Σ C X = C → Tree Σ (X × C)
-- Monad1 - C → ? × C
-- Monad2 - Tree Σ ?
-- KComp is the combination of Monad1 and Monad2
-- TODO: Prove the Kernel is also a Monad (in this file, possibly)

bind-kernel : ∀ {Σ C X Y} → (X → KComp Σ C Y) → KComp Σ C X → KComp Σ C Y
bind-kernel f K C = bind-tree (λ {(x , C') → f x C'}) (K C)

record Monad {l} : Set (lsuc l) where
  field
    -- carrier (object map) fo the Kleisli triple
    T       : Set → Set
    -- unit
    η       : {X : Set} → X → T X
    -- bind
    _>>=_   : {X Y : Set} → T X → (X → T Y) → T Y
    -- laws
    η-left  : {X Y : Set} (x : X) (f : X → T Y) → η x >>= f ≡ f x
    η-right : {X : Set} (c : T X) → c >>= η ≡ c
    >>=-assoc : {X Y Z : Set} (c : T X) (f : X → T Y) (g : Y → T Z)
              → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)



module _ {l} (Σ : Sig) where --TODO: Put this into a separate file

  η-right-Tree : {X : Set} (c : Tree Σ X) → bind-tree leaf c ≡ c
  η-right-Tree (leaf x) = refl
  η-right-Tree (node op p param c) = cong (node op p param) (fun-ext (λ res → η-right-Tree (c res)))

  >>=-assoc-Tree : {X Y Z : Set} (c : Tree Σ X) (f : X → Tree Σ Y)
      (g : Y → Tree Σ Z) →
      bind-tree g (bind-tree f c) ≡ bind-tree (λ x → bind-tree g (f x)) c
  >>=-assoc-Tree (leaf x) f g = refl
  >>=-assoc-Tree (node op p param c) f g = cong (node op p param) (fun-ext (λ res → >>=-assoc-Tree (c res) f g))


  TreeMonad : Monad {l}
  TreeMonad   = record {
    T         = Tree Σ ;
    η         = leaf ;
    _>>=_     = λ x f → bind-tree f x ;
    η-left    = λ x f → refl ;
    -- (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
    η-right   = η-right-Tree ;
    >>=-assoc = >>=-assoc-Tree }


  UMonad : Monad {l} --TODO: this is the same as TreeMonad
  UMonad = record {
    T         = UComp Σ ;
    η         = leaf ;
    _>>=_     = λ M f → bind-user f M ;
    η-left    = λ x f → refl ;
    η-right   = η-right-Tree ;
    >>=-assoc = >>=-assoc-Tree }


  KMonad : (C : Set) → Monad {l}
  KMonad C = record {
    T         = KComp Σ C ;
    η         = λ x c → leaf (x , c) ;
    _>>=_     = λ K f c → bind-kernel f K c ;
    η-left    = λ c f → refl ;
    η-right   = η-right-Kernel ;
    >>=-assoc = >>=-assoc-Kernel }
    where
      η-right-Kernel : {X : Set} (K : KComp Σ C X) → bind-kernel (λ x c → leaf (x , c)) K ≡ K --TODO: rename things as you go so that it makes sense
      η-right-Kernel K = fun-ext λ c → η-right-Tree (K c)

      >>=-assoc-Kernel : {X Y Z : Set} (K : KComp Σ C X) (f : X → KComp Σ C Y) (g : Y → KComp Σ C Z)
        → bind-kernel g (bind-kernel f K) ≡ bind-kernel (λ x → bind-kernel g (f x)) K
      >>=-assoc-Kernel K f g = fun-ext (λ c → >>=-assoc-Tree (K c) (λ { (x , c') → f x c' }) (λ { (y , c') → g y c' }))


--TODOs for next time (17. 12. 2024)
--1. Split Denotations.agda into 2 files, one file has all definitions regarding Monads, the other has the ⟦ ⟧ stuff, except the ⟦ ⟧g stuff (which goes with Monads).
--2. Use consistent fixed variable names. Then keep it consistent forevermore.
--3. Finish the definitions of the ⟦ ⟧-kernel and ⟦ ⟧-user
--- ^What is expected^ --
--3.5. Rewrite the ⟦ ⟧ stuff to use the Monad structure
--4. getenv, setenv and the equations they use (for the Kernel Monad), algebraic operations, algebraicity equation (for both monads)
--Optional: Read the literature already given. Most important is that the Runners paper is understood as much as possible, the rest is simply background reading to understand that.
--Keep track of things you do not understand. Danel's thesis will be useful for HOW to write your own thesis. The MFPS2013 paper will also be useful.
