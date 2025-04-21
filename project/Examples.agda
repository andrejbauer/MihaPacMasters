open import Level        renaming (zero to lzero; suc to lsuc)
import Contexts
open import Parameters
import Types
import Terms
import Monads
import Equations
import Denotations
import Sub-Validity
import Ren-Validity

module Examples (G : GTypes) (O : Ops G) where

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
open Ren-Validity G O

open import Data.Nat.Base
open import Validity

fun1 : ℕ → ℕ → ℕ
fun1 n m = (2 * n) + m

fun2 : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ
fun2 n m f = f n m 

Nats : {!   !} GTypes
Nats = {! record { Basetype = ? }  !}   