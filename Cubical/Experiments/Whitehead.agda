-- Towards generalized Whitehead products

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.Whitehead where

open import Cubical.Foundations.Everything

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.HomotopyGroup

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

σ : {ℓA : Level} (A : Pointed ℓA) → (typ A) → typ (Ω (∙Susp (typ A)))
σ A a = merid a ∙ sym (merid (pt A))

σ-pt : {ℓA : Level} (A : Pointed ℓA) → σ A (pt A) ≡ refl
σ-pt A = rCancel (merid (pt A))

module _ {ℓA ℓB ℓX} (A : Pointed ℓA) (B : Pointed ℓB) (X : Pointed ℓX) where

  from-path : (h : typ A → (∙Susp (typ B) →∙ X)) (a : typ A) (b : typ B)
    → Path (typ X) (h a .fst north) (pt X)
  from-path h a b = (λ i → h a .fst (σ B b i)) ∙ h a .snd

  from : (A →∙ (∙Susp (typ B) →∙ X , (λ _ → pt X) , refl))
         → ((join (typ A) (typ B) , inl (pt A)) →∙ X)
  fst (from (h , h∙)) (inl a) = h a .fst north
  fst (from (h , h∙)) (inr b) = pt X
  fst (from (h , h∙)) (push a b i) = from-path h a b i
  snd (from (h , h∙)) = h (pt A) .snd

  module _ (β : ∙Susp (typ B) →∙ X) where

    -- boundary map
    ∂ : (∙Susp (typ A) →∙ X) → (A →∙ (∙Susp (typ B) →∙ X , β))
    fst (fst (∂ (α , α∙)) a) = β .fst
    snd (fst (∂ (α , α∙)) a) = β .snd
      ∙ (sym α∙ ∙∙ (λ i → α (σ A a i)) ∙∙ α∙)
    fst (snd (∂ (α , α∙)) i) = β .fst
    snd (snd (∂ (α , α∙)) i) = {!!} -- ✓

    ξ-path : (γ : ∙Susp (typ B) →∙ X) → (b : typ B)
             → Path (typ X) (β .fst north) (γ .fst north)
    ξ-path (γ , γ∙) b = (λ i → β .fst (σ B b (~ i)))
              ∙∙ (β .snd ∙ sym γ∙)
              ∙∙ (λ i → γ (σ B b i))

    -- equivalence of components
    ξ : (∙Susp (typ B) →∙ X , β)
        →∙ (∙Susp (typ B) →∙ X , (λ _ → pt X) , refl)
    fst (fst ξ (γ , γ∙)) north = β .fst north
    fst (fst ξ (γ , γ∙)) south = γ north
    fst (fst ξ (γ , γ∙)) (merid b i) = ξ-path (γ , γ∙) b i
    snd (fst ξ (γ , γ∙)) = β .snd
    fst (snd ξ i) north = β .snd i
    fst (snd ξ i) south = β .snd i
    fst (snd ξ i) (merid b j) = {!!}-- ✓
    snd (snd ξ i) j = β .snd (i ∨ j)

    -- composition with ξ
    ζ : (A →∙ (∙Susp (typ B) →∙ X , β))
        → (A →∙ (∙Susp (typ B) →∙ X , (λ _ → pt X) , refl))
    ζ γ = ξ ∘∙ γ

    -- Whitehead product with β
    ρ-path : (α : ∙Susp (typ A) →∙ X) (a : typ A) (b : typ B)
             → Path (typ X) (β .fst north) (α .fst north)
    ρ-path (α , α∙) a b = (λ i → β .fst (σ B b i))
      ∙∙ (β .snd ∙ sym α∙)
      ∙∙ λ i → α (σ A a (~ i))

    ρ : (∙Susp (typ A) →∙ X) → ((join (typ A) (typ B) , inl (pt A)) →∙ X)
    fst (ρ (α , α∙)) (inl a) = β .fst north
    fst (ρ (α , α∙)) (inr b) = α north
    fst (ρ (α , α∙)) (push a b i) = ρ-path (α , α∙) a b i
    snd (ρ (α , α∙)) = β .snd

    thm-inr : (α : ∙Susp (typ A) →∙ X) (b : typ B) → α .fst north ≡ pt X
    thm-inr (α , α∙) b = (α∙ ∙ sym (β .snd))
      ∙∙ (λ j → β .fst (σ B b (~ j))) ∙∙ β .snd

    thm : (α : ∙Susp (typ A) →∙ X) → ρ α ≡ from (ζ (∂ α))
    fst (thm (α , α∙) i) (inl a) = β .fst north
    fst (thm (α , α∙) i) (inr b) = thm-inr (α , α∙) b i
    fst (thm (α , α∙) i) (push a b j) = {!!}
    snd (thm (α , α∙) i) = {!!}
