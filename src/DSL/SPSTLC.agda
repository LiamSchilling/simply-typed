{- The simply typed lambda calculus with product and sum types. -}

module DSL.SPSTLC where

open import Data.Fin using (Fin)
open import Data.Fin.Show using (show)
open import Data.HList using (HList; hmap; hlookup; forget-map)
open import Data.HSum using (HSum; here; next; smap; inject; case-of-with)
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
data Tm {ℓ} {α : Set ℓ} : Ctx α → Ty α → Set ℓ where
  var   : ∀ {Γ τ}     → Tm (τ ∷ Γ) τ
  ↑_    : ∀ {Γ τ τ'}  → Tm Γ τ → Tm (τ' ∷ Γ) τ
  lam   : ∀ {Γ τ τ'}  → Tm (τ ∷ Γ) τ' → Tm Γ (τ ⟶ τ')
  _·_   : ∀ {Γ τ τ'}  → Tm Γ (τ ⟶ τ') → Tm Γ τ → Tm Γ τ'
  tuple : ∀ {Γ τs}    → HList (Tm Γ) τs → Tm Γ (prod τs)
  _·>_  : ∀ {Γ τs}    → Tm Γ (prod τs) → ∀ i → Tm Γ (lookup τs i)
  _<·_  : ∀ {Γ τs}    → ∀ i → Tm Γ (lookup τs i) → Tm Γ (sum τs)
  cases : ∀ {Γ τs τ'} → Tm Γ (sum τs) → HList (λ τ → Tm (τ ∷ Γ) τ') τs → Tm Γ τ'

-- The weakening lemma for terms is derived trivially.
wkn-tm : ∀ {ℓ} → {α : Set ℓ} → Wkn (Tm {ℓ} {α})
wkn-tm _ = ↑_

-- Pretty-printing for terms.
{-# TERMINATING #-}
show-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → {τ : Ty α} → Tm Γ τ → String
show-tm var          = "x"
show-tm (↑ t)        = "↑ " + show-tm t
show-tm (lam t)      = "λ " + show-tm t
show-tm (t' · t)     = "(" + show-tm t' + ") (" + show-tm t + ")"
show-tm (tuple ts)   = "〈 " + intersperse " ; " (forget-map show-tm ts) + " 〉"
show-tm (t ·> i)     = "(" + show-tm t + ") · " + show i
show-tm (i <· t)     = show i + " · (" + show-tm t + ")"
show-tm (cases t ts) = "cases " + show-tm t +
                       " { " + intersperse " | " (forget-map show-tm ts) + " }"

-- The interpretation of a type variable back into the semantic domain of term syntax.
syn-itp : ∀ {ℓ} → {α : Set ℓ} → Itp ℓ α
syn-itp Γ a = Tm Γ (atom a)

-- The weakening lemma for the syntax interpretation is also derived trivially.
wkn-syn : ∀ {ℓ} → {α : Set ℓ} → Wkn (syn-itp {ℓ} {α})
wkn-syn _ = ↑_

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

-- The semantic denotation of a type into a meta-level type
-- with respect to an interpretation of the type variables,
-- all indexed by the typing context.
-- Note that weakening must be baked into the definition of the arrow case.
{-# TERMINATING #-}
dnt-ty : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Dnt (ℓ ⊔ ℓ') α (Ty α)
dnt-ty φ Γ (atom a)  = dnt-itp φ Γ a
dnt-ty φ Γ (τ ⟶ τ') = ∀ {Γ'} → dnt-ty φ (Γ' ++ Γ) τ → dnt-ty φ (Γ' ++ Γ) τ'
dnt-ty φ Γ (prod τs) = HList (dnt-ty φ Γ) τs
dnt-ty φ Γ (sum τs)  = HSum (dnt-ty φ Γ) τs

-- The semantic denotation of a typing context is the conjunction of the denotations of its types.
dnt-ctx : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Dnt (ℓ ⊔ ℓ') α (Ctx α)
dnt-ctx φ Γ = HCtx (dnt-ty φ Γ)

-- Given that weakening holds for the type variable interpretation,
-- we can show that it holds for the semantic domain of terms.
{-# TERMINATING #-}
dnt-wkn : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) → Wkn φ → Wkn (dnt-ty φ)
dnt-wkn φ wkn           (atom a)  σ = into-itp φ (wkn a (out-itp φ σ))
dnt-wkn φ wkn {Γ} {τ''} (τ ⟶ τ') σ {Γ'} rewrite sym (++-assoc Γ' [ τ'' ] Γ) = σ {Γ' ∷ʳ τ''}
dnt-wkn φ wkn           (prod τs) σ = hmap (λ {τ} → dnt-wkn φ wkn τ) σ
dnt-wkn φ wkn           (sum τs)  σ = smap (λ {τ} → dnt-wkn φ wkn τ) σ

-- The semantic denotation of a term into a meta-level term
-- given the denotation of its context.
-- This proves stability with respect to our type-level denotations.
{-# TERMINATING #-}
dnt-tm : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) →
         Wkn φ → ∀ {Γ Γ' τ} → dnt-ctx φ Γ Γ' → Tm Γ' τ → dnt-ty φ Γ τ
dnt-tm φ wkn (σ ∷ _) var          = σ
dnt-tm φ wkn (_ ∷ Σ) (↑ t)        = dnt-tm φ wkn Σ t
dnt-tm φ wkn Σ       (lam t)      = λ σ → dnt-tm φ wkn
                                    (σ ∷ hmap (λ {τ} → iter-wkn (dnt-ty φ) (dnt-wkn φ wkn) τ) Σ) t
dnt-tm φ wkn Σ       (t' · t)     = dnt-tm φ wkn Σ t' (dnt-tm φ wkn Σ t)
dnt-tm φ wkn Σ       (tuple ts)   = hmap (dnt-tm φ wkn Σ) ts
dnt-tm φ wkn Σ       (t ·> i)     = hlookup (dnt-tm φ wkn Σ t) i
dnt-tm φ wkn Σ       (i <· t)     = inject i (dnt-tm φ wkn Σ t)
dnt-tm φ wkn Σ       (cases t ts) = case-of-with ts (dnt-tm φ wkn Σ t)
                                    (λ t' σ → dnt-tm φ wkn (σ ∷ Σ) t')
