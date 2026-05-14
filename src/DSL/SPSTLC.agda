{- The simply typed lambda calculus with product and sum types. -}

module DSL.SPSTLC where

open import Data.Fin using (Fin)
open import Data.Fin.Show using (show)
open import Data.HList using (HList; hmap; forget)
open import Data.List using (List; [_]; _∷ʳ_; map; length; lookup)
open import Data.List.Properties using (++-assoc)
open import Data.String using (String; intersperse) renaming (_++_ to _+_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Level using (_⊔_)
import TypeSystem

infixr 10 _⟶_
infixl 10 _·_
infixl 9 _·>_
infixr 9 _<·_

----------------------------------------------------------------------------------------------------
-- Types
----------------------------------------------------------------------------------------------------

-- Simple types with type variable atoms.
data Ty {ℓ} (α : Set ℓ) : Set ℓ where
  atom : α → Ty α
  _⟶_ : Ty α → Ty α → Ty α
  prod : List (Ty α) → Ty α
  sum  : List (Ty α) → Ty α

open module TS = TypeSystem Ty public

-- Pretty-printing for types.
{-# TERMINATING #-}
show-ty : ∀ {ℓ} → {α : Set ℓ} → (α → String) → Ty α → String
show-ty show (atom a)        = show a
show-ty show (τ ⟶ τ')       = "(" + show-ty show τ + " → " + show-ty show τ' + ")"
show-ty show (prod [])       = "unit"
show-ty show (prod (τ ∷ [])) = show-ty show τ + " prod"
show-ty show (prod τs)       = "(" + intersperse " * " (map (show-ty show) τs) + ")"
show-ty show (sum [])        = "void"
show-ty show (sum (τ ∷ []))  = show-ty show τ + " sum"
show-ty show (sum τs)        = "(" + intersperse " + " (map (show-ty show) τs) + ")"

----------------------------------------------------------------------------------------------------
-- Terms
----------------------------------------------------------------------------------------------------

-- The abstract syntax of terms, intrinsically typed with respect to a typing context.
-- We prefer the nameless representation with explicit weakening over De Bruijn indices
-- because it gives us the weakening lemma for free and makes its computation effectively lazy.
-- Note that the type of `Tm` is equivalently stated as `Dnt ℓ α (Ty α)`,
-- and the type of `↑_` is equivalently stated as `Wkn Tm`.
data Tm {ℓ} {α : Set ℓ} : Ctx α → Ty α → Set ℓ where
  var   : ∀ {Γ τ}     → Tm (τ ∷ Γ) τ
  ↑_    : ∀ {Γ τ τ'}  → Tm Γ τ → Tm (τ' ∷ Γ) τ
  lam   : ∀ {Γ τ τ'}  → Tm (τ ∷ Γ) τ' → Tm Γ (τ ⟶ τ')
  _·_   : ∀ {Γ τ τ'}  → Tm Γ (τ ⟶ τ') → Tm Γ τ → Tm Γ τ'
  tuple : ∀ {Γ τs}    → HList (Tm Γ) τs → Tm Γ (prod τs)
  _·>_  : ∀ {Γ τs}    → Tm Γ (prod τs) → ∀ i → Tm Γ (lookup τs i)
  _<·_  : ∀ {Γ τs}    → ∀ i → Tm Γ (lookup τs i) → Tm Γ (sum τs)
  cases : ∀ {Γ τs τ'} → Tm Γ (sum τs) → HList (λ τ → Tm (τ ∷ Γ) τ') τs → Tm Γ τ'

-- Pretty-printing for terms.
{-# TERMINATING #-}
show-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → {τ : Ty α} → Tm Γ τ → String
show-tm var          = "x"
show-tm (↑ t)        = "↑ " + show-tm t
show-tm (lam t)      = "λ " + show-tm t
show-tm (t' · t)     = "(" + show-tm t' + ") (" + show-tm t + ")"
show-tm (tuple ts)   = "〈 " + intersperse " ; " (forget (hmap show-tm ts)) + " 〉"
show-tm (t ·> i)     = "(" + show-tm t + ") · " + show i
show-tm (i <· t)     = show i + " · (" + show-tm t + ")"
show-tm (cases t ts) = "cases " + show-tm t +
                       " { " + intersperse " | " (forget (hmap show-tm ts)) + " }"

-- The interpretation of a type variable back into the semantic domain of terms.
syn-itp : ∀ {ℓ} → {α : Set ℓ} → Itp ℓ α
syn-itp Γ a = Tm Γ (atom a)
