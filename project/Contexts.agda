open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Parameters

module Contexts where 

open import Types 
 
open GTypes G
open Ops O
 
-- Contexts (using De Bruijn indices)
data Ctx : Set where
  []  : Ctx
  _∷_ : Ctx → VType → Ctx
 
-- Variables in context
data _∈_ : VType → Ctx → Set where                         -- x : X ∈ Γ
  here  : {X : VType} {Γ : Ctx} → X ∈ (Γ ∷ X)
  there : {X Y : VType} {Γ : Ctx} → X ∈ Γ → X ∈ (Γ ∷ Y)
 
infixl 20 _∷_
