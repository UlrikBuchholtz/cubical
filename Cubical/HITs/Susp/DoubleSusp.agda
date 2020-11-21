{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Susp.DoubleSusp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Cubical.Data.Bool
open import Cubical.HITs.Join
open import Cubical.HITs.Susp.Base

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    A' : Type ℓ'

neg : Susp A → Susp A
neg north = south
neg south = north
neg (merid a i) = (merid a ⁻¹) i

SuspFun : (A → A') → Susp A → Susp A'
SuspFun f north = north
SuspFun f south = south
SuspFun f (merid a i) = merid (f a) i

module NegNegCube {ℓ : Level} (A : Type ℓ) where
  left-sq : {x y : A} {p q : x ≡ y} (α : p ≡ q) → Square
            q p refl refl
  left-sq α i j = α (~ i) j

  right-sq : {x y : A} {p q : x ≡ y} (α : p ≡ q) → Square
             (p ⁻¹) (q ⁻¹) refl refl
  right-sq α i j = α i (~ j)

  front-sq : {x y z : A} (q : x ≡ y) (p : y ≡ z) → Square q p q p
  front-sq {x = x} {y = y} q p =
    J P (J (λ y' q' → Square q' refl q' refl) refl q) p
    where
      P : (z' : A) → (p' : y ≡ z') → Type _
      P z' p' = Square q p' q p'

  back-sq : {x y z : A} (p : x ≡ y) (q : x ≡ z) → Square
            p (q ⁻¹) q (p ⁻¹)
  back-sq {x = x} {y = y} p q =
    J (P y p) (J (λ y' p' → P y' p' x refl) refl p) q
    where
      P : (y' : A) → (p' : x ≡ y') → (z' : A) → (p' : x ≡ z') → Type _
      P y' p' z' q' = Square p' (q' ⁻¹) q' (p' ⁻¹)

  bottom-sq : {x y : A} (q : x ≡ y) → Square refl refl q q
  bottom-sq q i j = q i

  top-sq : {x y : A} (p : x ≡ y) → Square refl refl (p ⁻¹) (p ⁻¹)
  top-sq p i j = p (~ i)

  cube : {x y : A} {p q : x ≡ y} (α : p ≡ q) → Cube
         (left-sq α) (right-sq α)
         (front-sq q (p ⁻¹)) (back-sq p q)
         (bottom-sq q) (top-sq p)
  cube {x = x} {y = y} {p = p} {q = q} α =
    J (P y p) (J (λ y' p' → P y' p' p' refl) r p) α
      where
        P : (y' : A) → (p' q' : x ≡ y') → (α' : p' ≡ q') → Type _
        P y' p' q' α' = Cube
          (left-sq α') (right-sq α') (front-sq q' (p' ⁻¹)) (back-sq p' q')
          (bottom-sq q') (top-sq p')
        r : P x refl refl refl
        r i j k = back-sq {y = x} {z = x} refl refl i k

module _ {ℓ : Level} (A : Type ℓ) where

  open NegNegCube (Susp (Susp A))

  SuspNegNeg : (x : Susp (Susp A)) → SuspFun neg x ≡ neg x
  SuspNegNeg north i = merid south i  -- k = i0
  SuspNegNeg south i = merid north (~ i) -- k = i1
  SuspNegNeg (merid north k) i = front-sq (merid south) (merid north ⁻¹) i k -- j = i0
  SuspNegNeg (merid south k) i = back-sq (merid north) (merid south) i k -- j = i1
  SuspNegNeg (merid (merid a j) k) i = cube α i j k
    where
      α : Path (Path (Susp (Susp A)) north south) (merid north) (merid south)
      α i j = merid (merid a i) j
