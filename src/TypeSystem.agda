module TypeSystem (Ty : ∀ {ℓ} → Set ℓ → Set ℓ) where

open import Data.HList using (HList)
open import Data.HList using ([]; _∷_) public
open import Data.List using (List)
open import Data.List using ([]; _∷_; _++_) public
open import Level using (Level; suc; _⊔_; Lift; lift; lower)

----------------------------------------------------------------------------------------------------
-- Contexts
----------------------------------------------------------------------------------------------------

-- A typing context is an ordered list of accessible types.
Ctx : ∀ {ℓ} → Set ℓ → Set ℓ
Ctx α = List (Ty α)

-- A context whose elements are typed heterogenously with respect to a base context.
HCtx : ∀ {ℓ ℓ'} → {α : Set ℓ} → (Ty α → Set ℓ') → Ctx α → Set ℓ'
HCtx = HList

----------------------------------------------------------------------------------------------------
-- Type denotations and type variable interpretations
----------------------------------------------------------------------------------------------------

-- Denotations of type-like objects into meta-level types, indexed by the typing context.
Dnt : ∀ {ℓ ℓ'} ℓ'' → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ' ⊔ suc ℓ'')
Dnt ℓ'' α β = Ctx α → β → Set ℓ''

-- Interpretations of type variable atoms into meta-level types, indexed by the typing context.
Itp : ∀ {ℓ} ℓ' → Set ℓ → Set (ℓ ⊔ suc ℓ')
Itp ℓ' α = Dnt ℓ' α α

-- Lift a type variable interpretation to the level of type object denotations.
dnt-itp : ∀ {ℓ ℓ'} → {α : Set ℓ} → Itp ℓ' α → Itp (ℓ ⊔ ℓ') α
dnt-itp {ℓ} {ℓ'} φ Γ a = Lift (ℓ ⊔ ℓ') (φ Γ a)

-- Transport a member of an interpretation into a member of an interpretation denotation.
into-itp : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) → ∀ {Γ a} → φ Γ a → dnt-itp φ Γ a
into-itp _ = lift

-- Transport a member of an interpretation denotation into a member of an interpretation.
out-itp : ∀ {ℓ ℓ'} → {α : Set ℓ} (φ : Itp ℓ' α) → ∀ {Γ a} → dnt-itp φ Γ a → φ Γ a
out-itp _ = lower

----------------------------------------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------------------------------------

-- The statement that weakening holds for a denotation of type objects.
Wkn : ∀ {ℓ ℓ' ℓ''} → {α : Set ℓ} {β : Set ℓ'} → Dnt ℓ'' α β → Set (ℓ ⊔ ℓ' ⊔ ℓ'')
Wkn φ = ∀ {Γ τ'} b → φ Γ b → φ (τ' ∷ Γ) b

-- Transforms weakening into an n-fold version.
iter-wkn : ∀ {ℓ ℓ' ℓ''} → {α : Set ℓ} {β : Set ℓ'} (φ : Dnt ℓ'' α β) →
           Wkn φ → ∀ {Γ Γ'} b → φ Γ b → φ (Γ' ++ Γ) b
iter-wkn φ wkn {Γ' = []}     b σ = σ
iter-wkn φ wkn {Γ' = _ ∷ Γ'} b σ = wkn b (iter-wkn φ wkn b σ)
