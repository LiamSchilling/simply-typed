module TypeSystem (Ty : ∀ {ℓ} → Set ℓ → Set ℓ) where

open import Data.HList using (HList)
open import Data.HList using ([]; _∷_; hmap) public
open import Data.List using (List)
open import Data.List using ([]; _∷_; _∷ʳ_; _++_; [_]; map) public
open import Level using (Lift; lift; lower)
open import Level using (suc; _⊔_) public

-- A typing context is an ordered list of accessible types.
Ctx : ∀ {ℓ} → Set ℓ → Set ℓ
Ctx α = List (Ty α)

-- A context whose elements are typed heterogenously with respect to a base context.
HCtx : ∀ {ℓ ℓ'} → {α : Set ℓ} → (Ty α → Set ℓ') → Ctx α → Set ℓ'
HCtx = HList

-- Interpretations of type variables into meta-level types, indexed by the typing context.
Itp : ∀ ℓ' {ℓ} → Set ℓ → Set (ℓ ⊔ suc ℓ')
Itp ℓ' α = Ctx α → α → Set ℓ'

-- For use in semantic denotations of types using type variable interpretations,
-- simply lifting the interpretation to a universe that also contains the type variables.
denote-itp : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Itp (ℓ ⊔ ℓ') α
denote-itp {ℓ} {ℓ'} φ Γ a = Lift (ℓ ⊔ ℓ') (φ Γ a)

-- Transport a member of an interpretation into a member of an interpretation denotation.
into-itp : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) → ∀ {Γ a} → φ Γ a → denote-itp φ Γ a
into-itp _ = lift

-- Transport a member of an interpretation denotation into a member of an interpretation.
out-itp : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) → ∀ {Γ a} → denote-itp φ Γ a → φ Γ a
out-itp _ = lower

-- The statement that weakening holds for an interpretation of type variables.
Weakening : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Set (ℓ ⊔ ℓ')
Weakening φ = ∀ {Γ a τ'} → denote-itp φ Γ a → denote-itp φ (τ' ∷ Γ) a
