{-# OPTIONS --guardedness #-}

module Main where

open import Data.Nat
open import Data.Fin
import DSL.STLC
open import DSL.SPSTLC
import DSL.MKSTLC
import DSL.KSTLC
open import IO

ty : Ty ℕ
ty = sum (atom 0 ⟶ atom 1 ∷ atom 0 ⟶ atom 2 ∷ []) ⟶ atom 0 ⟶ sum (atom 1 ∷ atom 2 ∷ [])

tm : Tm [] ty
tm = lam (lam (cases (↑ var) (# 0 <· var · ↑ var ∷ # 1 <· var · ↑ var ∷ [])))

--normal-tm : Tm [] ty
--normal-tm = normalize-tm [] tm

main : Main
main = run (putStrLn (show-tm tm))
