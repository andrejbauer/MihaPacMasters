open import Parameters

module Replace (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open import Types G O
open import Terms G O
open import Contexts G O

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ' → Γ ⊢V: X
Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : VType} → X ∈ Γ' → X ∈ Γ

_[_↦_] : ?

_[here↦_] : ?
