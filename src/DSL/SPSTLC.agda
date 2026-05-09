{- The simply typed lambda calculus with product and sum types. -}

module DSL.SPSTLC where

open import Data.List using (List)
open import Data.String using (String; intersperse) renaming (_++_ to _+_)
open import Relation.Binary.PropositionalEquality using (sym)
import TypeSystem

infixr 5 _⟶_
--infixl 10 _·_

----------------------------------------------------------------------------------------------------
-- Types
----------------------------------------------------------------------------------------------------

-- Simple types with type variable atoms.
data Ty {ℓ} (α : Set ℓ) : Set ℓ where
  atom : α → Ty α
  _⟶_ : Ty α → Ty α → Ty α
  prod : List (Ty α) → Ty α
  sum : List (Ty α) → Ty α

open module TS = TypeSystem Ty public

-- Pretty-printing for types.
{-# TERMINATING #-}
show-ty : ∀ {ℓ} → {α : Set ℓ} → (α → String) → Ty α → String
show-ty show (atom a) = show a
show-ty show (τ ⟶ τ') = "(" + show-ty show τ + " → " + show-ty show τ' + ")"
show-ty show (prod []) = "unit"
show-ty show (prod (τ ∷ [])) = show-ty show τ + " prod"
show-ty show (prod τs) = "(" + intersperse " * " (map (show-ty show) τs) + ")"
show-ty show (sum []) = "void"
show-ty show (sum (τ ∷ [])) = show-ty show τ + " sum"
show-ty show (sum τs) = "(" + intersperse " + " (map (show-ty show) τs) + ")"
