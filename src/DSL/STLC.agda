{- The simply typed lambda calculus. -}

module DSL.STLC where

open import Data.List.Properties using (++-assoc)
open import Data.String using (String) renaming (_++_ to _+_)
open import Relation.Binary.PropositionalEquality using (sym)
import TypeSystem

infixr 5 _⟶_
infixl 10 _·_

-- Simple types with type variable atoms.
data Ty {ℓ} (α : Set ℓ) : Set ℓ where
  atom : α → Ty α
  _⟶_ : Ty α → Ty α → Ty α

open module TS = TypeSystem Ty public

show-ty : ∀ {ℓ} → {α : Set ℓ} → (α → String) → Ty α → String
show-ty show (atom a) = show a
show-ty show (τ ⟶ τ') = "(" + show-ty show τ + " ⟶ " + show-ty show τ' + ")"

-- The abstract syntax of terms, intrinsically typed with respect to a typing context.
-- We prefer the nameless representation with explicit weakening over De Bruijn indices
-- because it gives us the weakening lemma for free and makes its computation effectively lazy.
data Tm {ℓ} {α : Set ℓ} : Ctx α → Ty α → Set ℓ where
  var : ∀ {Γ τ} → Tm (τ ∷ Γ) τ
  ↑_ : ∀ {Γ τ τ'} → Tm Γ τ → Tm (τ' ∷ Γ) τ
  lam : ∀ {Γ τ τ'} → Tm (τ ∷ Γ) τ' → Tm Γ (τ ⟶ τ')
  _·_ : ∀ {Γ τ τ'} → Tm Γ (τ ⟶ τ') → Tm Γ τ → Tm Γ τ'

show-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → {τ : Ty α} → Tm Γ τ → String
show-tm var = "x"
show-tm (↑ t) = "↑ " + show-tm t
show-tm (lam t) = "λ " + show-tm t
show-tm (t' · t) = "(" + show-tm t' + ") · (" + show-tm t + ")"

-- An n-fold version of `↑_`.
⇑_ : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ Γ'} → {τ : Ty α} → Tm Γ τ → Tm (Γ' ++ Γ) τ
⇑_ {Γ' = []} t = t
⇑_ {Γ' = _ ∷ Γ'} t = ↑ ⇑ t

-- The interpretation of a type variable back into the semantic domain of terms.
syntax-itp : ∀ {ℓ} → {α : Set ℓ} → Itp ℓ α
syntax-itp Γ a = Tm Γ (atom a)

-- Weakening holds for the syntactic interpretation of type variables.
syntax-weakening : ∀ {ℓ} → {α : Set ℓ} → Weakening (syntax-itp {ℓ} {α})
syntax-weakening σ = into-itp syntax-itp (↑ out-itp syntax-itp σ)

-- The semantic denotation of a type into a meta-level type
-- with respect to an interpretation of the type variables,
-- all indexed by the typing context.
-- Note that weakening must be baked into the definition of the arrow case.
denote-ty : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Ctx α → Ty α → Set (ℓ ⊔ ℓ')
denote-ty φ Γ (atom a) = denote-itp φ Γ a
denote-ty φ Γ (τ ⟶ τ') = ∀ {Γ'} → denote-ty φ (Γ' ++ Γ) τ → denote-ty φ (Γ' ++ Γ) τ' 

-- The semantic denotation of a typing context is the conjunction of the denotations of its types.
denote-ctx : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Ctx α → Ctx α → Set (ℓ ⊔ ℓ')
denote-ctx φ Γ = HCtx (denote-ty φ Γ)

-- Given that weakening holds for the interpretation of the type variables,
-- we can show that it holds for our semantic domain.
denote-weaken : ∀ {ℓ ℓ'} → {α : Set ℓ} {φ : Itp ℓ' α} → Weakening φ → ∀ {Γ τ'} → (τ : Ty α) → denote-ty φ Γ τ → denote-ty φ (τ' ∷ Γ) τ
denote-weaken W (atom a) = W
denote-weaken W {Γ} {τ''} (τ ⟶ τ') σ {Γ'} rewrite sym (++-assoc Γ' [ τ'' ] Γ) = σ {Γ' ∷ʳ τ''}

-- An n-fold version of `denote-weaken`.
denote-many-weaken : ∀ {ℓ ℓ'} → {α : Set ℓ} {φ : Itp ℓ' α} → Weakening φ → ∀ {Γ Γ'} → (τ : Ty α) → denote-ty φ Γ τ → denote-ty φ (Γ' ++ Γ) τ
denote-many-weaken W {Γ' = []} τ σ = σ
denote-many-weaken W {Γ' = _ ∷ Γ'} τ σ = denote-weaken W τ (denote-many-weaken W τ σ)

-- The semantic denotation of a term into a meta-level term
-- given the denotation of its context.
-- This proves stability with respect to our type-level denotations.
denote-tm : ∀ {ℓ ℓ'} → {α : Set ℓ} {φ : Itp ℓ' α} → Weakening φ → ∀ {Γ Γ'} → (τ : Ty α) → denote-ctx φ Γ Γ' → Tm Γ' τ → denote-ty φ Γ τ
denote-tm W τ (σ ∷ _) var = σ
denote-tm W τ (_ ∷ Σ) (↑ t) = denote-tm W τ Σ t
denote-tm W (τ ⟶ τ') Σ (lam t) σ = denote-tm W τ' (σ ∷ hmap (denote-many-weaken W) _ Σ) t
denote-tm W τ' Σ (t' · t) = denote-tm W (_ ⟶ τ') Σ t' (denote-tm W _ Σ t)

-- The reification of a semantic object back into a term (`quote-tm`),
-- defined mutually with the reflection of a term into the semantic domain (`reflect-tm`),
-- all using the interpretation of a type variable as opaque term syntax.
-- This proves completeness with respect to our type-level denotations.
quote-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → (τ : Ty α) → denote-ty syntax-itp Γ τ → Tm Γ τ
reflect-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ} → (τ : Ty α) → Tm Γ τ → denote-ty syntax-itp Γ τ
quote-tm (atom a) σ = out-itp syntax-itp σ
quote-tm (τ ⟶ τ') σ = lam (quote-tm τ' (σ (reflect-tm τ var)))
reflect-tm (atom a) t = into-itp syntax-itp t
reflect-tm (τ ⟶ τ') t' σ = reflect-tm τ' (⇑ t' · quote-tm τ σ)

-- Normalize a term by denoting it into a canonical object in the semantic domain,
-- then reifying it back into a term.
normalize-tm : ∀ {ℓ} → {α : Set ℓ} → ∀ {Γ Γ'} → (τ : Ty α) → denote-ctx syntax-itp Γ Γ' → Tm Γ' τ → Tm Γ τ
normalize-tm τ Σ t = quote-tm τ (denote-tm syntax-weakening τ Σ t)
