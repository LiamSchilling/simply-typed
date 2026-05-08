{-# OPTIONS --guardedness #-}

module Main where

open import Data.Nat
open import DSL.STLC
open import IO

ty : Ty ℕ
ty = (atom 0 ⟶ atom 1) ⟶ (atom 0 ⟶ atom 1)

tm : Tm [] ty
tm = lam var

normal-tm : Tm [] ty
normal-tm = normalize-tm ty [] tm

main : Main
main = run (putStrLn (show-tm normal-tm))
