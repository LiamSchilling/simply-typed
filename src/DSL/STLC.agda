{- The simply typed lambda calculus. -}

module DSL.STLC where

open import Data.HList using (hmap)
open import Data.List using ([_]; _∷ʳ_)
open import Data.List.Properties using (++-assoc)
open import Data.String using (String) renaming (_++_ to _+_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Level using (_⊔_)
import TypeSystem

infixr 10 _⟶_
infixl 10 _·_

----------------------------------------------------------------------------------------------------
-- Types
----------------------------------------------------------------------------------------------------

-- Simple types with type variable atoms.
data Ty {ℓ} (α : Set ℓ) : Set ℓ where
  atom : α → Ty α
  _⟶_ : Ty α → Ty α → Ty α

open module TS = TypeSystem Ty public

-- Pretty-printing for types.
show-ty : ∀ {ℓ} → {α : Set ℓ} → (α → String) → Ty α → String
show-ty show (atom a)  = show a
show-ty show (τ ⟶ τ') = "(" + show-ty show τ + " → " + show-ty show τ' + ")"

----------------------------------------------------------------------------------------------------
-- Terms
----------------------------------------------------------------------------------------------------

-- The abstract syntax of terms, intrinsically typed with respect to a typing context.
-- We prefer the nameless representation with explicit weakening over De Bruijn indices
-- because it gives us the weakening lemma for free and makes its computation effectively lazy.
-- Note that the type of `Tm` is equivalently stated as `Dnt ℓ α (Ty α)`,
-- and the type of `↑_` is equivalently stated as `Wkn Tm`.
data Tm {ℓ} {α : Set ℓ} : Ctx α → Ty α → Set ℓ where
  var : ∀ {Γ τ}    → Tm (τ ∷ Γ) τ
  ↑_  : ∀ {Γ τ τ'} → Tm Γ τ → Tm (τ' ∷ Γ) τ
  lam : ∀ {Γ τ τ'} → Tm (τ ∷ Γ) τ' → Tm Γ (τ ⟶ τ')
  _·_ : ∀ {Γ τ τ'} → Tm Γ (τ ⟶ τ') → Tm Γ τ → Tm Γ τ'

-- Pretty-printing for terms.
show-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → {τ : Ty α} → Tm Γ τ → String
show-tm var      = "x"
show-tm (↑ t)    = "↑ " + show-tm t
show-tm (lam t)  = "λ " + show-tm t
show-tm (t' · t) = "(" + show-tm t' + ") (" + show-tm t + ")"

-- The interpretation of a type variable back into the semantic domain of terms.
syn-itp : ∀ {ℓ} → {α : Set ℓ} → Itp ℓ α
syn-itp Γ a = Tm Γ (atom a)

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

-- The semantic denotation of a type into a meta-level type
-- with respect to an interpretation of the type variables,
-- all indexed by the typing context.
-- Note that weakening must be baked into the definition of the arrow case.
dnt-ty : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Dnt (ℓ ⊔ ℓ') α (Ty α)
dnt-ty φ Γ (atom a)  = dnt-itp φ Γ a
dnt-ty φ Γ (τ ⟶ τ') = ∀ {Γ'} → dnt-ty φ (Γ' ++ Γ) τ → dnt-ty φ (Γ' ++ Γ) τ' 

-- The semantic denotation of a typing context is the conjunction of the denotations of its types.
dnt-ctx : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Dnt (ℓ ⊔ ℓ') α (Ctx α)
dnt-ctx φ Γ = HCtx (dnt-ty φ Γ)

-- Given that weakening holds for the type variable interpretation,
-- we can show that it holds for the semantic domain of terms.
dnt-wkn : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) → Wkn φ → Wkn (dnt-ty φ)
dnt-wkn φ wkn {Γ} {atom a}  {τ'}  σ      = into-itp φ (wkn (out-itp φ σ))
dnt-wkn φ wkn {Γ} {τ ⟶ τ'} {τ''} σ {Γ'} rewrite sym (++-assoc Γ' [ τ'' ] Γ) = σ {Γ' ∷ʳ τ''}

-- The semantic denotation of a term into a meta-level term
-- given the denotation of its context.
-- This proves stability with respect to our type-level denotations.
dnt-tm : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) →
         Wkn φ → ∀ {Γ Γ' τ} → dnt-ctx φ Γ Γ' → Tm Γ' τ → dnt-ty φ Γ τ
dnt-tm φ wkn (σ ∷ _) var      = σ
dnt-tm φ wkn (_ ∷ Σ) (↑ t)    = dnt-tm φ wkn Σ t
dnt-tm φ wkn Σ       (lam t)  = λ σ →
                                dnt-tm φ wkn (σ ∷ hmap (iter-wkn (dnt-ty φ) (dnt-wkn φ wkn)) Σ) t
dnt-tm φ wkn Σ       (t' · t) = dnt-tm φ wkn Σ t' (dnt-tm φ wkn Σ t)

----------------------------------------------------------------------------------------------------
-- Normalization
----------------------------------------------------------------------------------------------------

-- The reification of a semantic object back into a term (`quote-tm`),
-- defined mutually with the reflection of a term into the semantic domain (`reflect-tm`),
-- all using the interpretation of a type variable as opaque term syntax.
-- This proves completeness with respect to our type-level denotations.
quote-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → (τ : Ty α) → dnt-ty syn-itp Γ τ → Tm Γ τ
reflect-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → (τ : Ty α) → Tm Γ τ → dnt-ty syn-itp Γ τ
quote-tm   (atom a)  σ  = out-itp syn-itp σ
quote-tm   (τ ⟶ τ') σ  = lam (quote-tm τ' (σ (reflect-tm τ var)))
reflect-tm (atom a)  t  = into-itp syn-itp t
reflect-tm (τ ⟶ τ') t' = λ σ → reflect-tm τ' (iter-wkn Tm ↑_ t' · quote-tm τ σ)

-- Normalize a term by denoting it into a canonical object in the semantic domain,
-- then reifying it back into a term.
normalize-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ Γ'} → {τ : Ty α} → dnt-ctx syn-itp Γ Γ' → Tm Γ' τ → Tm Γ τ
normalize-tm {τ = τ} Σ t = quote-tm τ (dnt-tm syn-itp ↑_ Σ t)
