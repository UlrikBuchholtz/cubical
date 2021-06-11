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

∙join : ∀ {ℓA ℓB} → Pointed ℓA → Pointed ℓB → Pointed (ℓ-max ℓA ℓB)
fst (∙join A B) = join (typ A) (typ B)
snd (∙join A B) = inl (pt A)

module _ {ℓA ℓB ℓX} (A : Pointed ℓA) (B : Pointed ℓB) (X : Pointed ℓX) where

  φ-path : (h : typ A → (∙Susp (typ B) →∙ X)) (a : typ A) (b : typ B)
    → Path (typ X) (h a .fst north) (pt X)
  φ-path h a b = (cong (h a .fst) (σ B b)) ∙ h a .snd

  φ : (A →∙ (∙Susp (typ B) →∙ X ∙)) → (∙join A B →∙ X)
  fst (φ (h , h∙)) (inl a) = h a .fst north
  fst (φ (h , h∙)) (inr b) = pt X
  fst (φ (h , h∙)) (push a b i) = φ-path h a b i
  snd (φ (h , h∙)) = h (pt A) .snd

  module _ (β : ∙Susp (typ B) →∙ X) where

    -- boundary map
    ∂ : (∙Susp (typ A) →∙ X) → (A →∙ (∙Susp (typ B) →∙ X , β))
    fst (fst (∂ (α , α∙)) a) = β .fst
    snd (fst (∂ (α , α∙)) a) = β .snd
      ∙ (sym α∙ ∙∙ (λ i → α (σ A a i)) ∙∙ α∙)
    fst (snd (∂ (α , α∙)) i) = β .fst
    snd (snd (∂ (α , α∙)) i) j =
      hcomp (λ k → λ { (i = i0) → doubleCompPath-filler refl (β .snd)
                          (sym α∙ ∙∙ cong α (σ A (pt A)) ∙∙ α∙) k j
                     ; (i = i1) → β .snd j
                     ; (j = i0) → β .fst north
                     ; (j = i1) → sq i k }) (β .snd j)
      where
        sq : Square (sym α∙ ∙∙ cong α (σ A (pt A)) ∙∙ α∙) refl refl refl
        sq i j =
          hcomp (λ k → λ { (i = i0) → doubleCompPath-filler (sym α∙)
                              (cong α (σ A (pt A))) α∙ k j
                         ; (i = i1) → α∙ k
                         ; (j = i0) → α∙ k
                         ; (j = i1) → α∙ k }) (α (σ-pt A i j))

    ξ-path : (γ : ∙Susp (typ B) →∙ X) → (b : typ B)
             → Path (typ X) (β .fst north) (γ .fst north)
    ξ-path (γ , γ∙) b = (λ i → β .fst (σ B b (~ i)))
              ∙∙ (β .snd ∙ sym γ∙)
              ∙∙ (λ i → γ (σ B b i))

    ξ-path-id : (b : typ B) → ξ-path β b ≡ refl
    ξ-path-id b =
      ξ-path β b
        ≡⟨ cong (λ q → sym p ∙∙ q ∙∙ p) (rCancel (β .snd))  ⟩
      sym p ∙∙ refl ∙∙ p
        ≡⟨ doubleCompPath-elim (sym p) refl p ⟩
      (sym p ∙ refl) ∙ p ≡⟨ cong (λ q → q ∙ p) ((sym (rUnit (sym p)))) ⟩
      sym p ∙ p ≡⟨ lCancel p ⟩
      refl ∎
      where
        p : β .fst north ≡ β .fst north
        p = cong (β .fst) (σ B b)

    -- equivalence of components
    ξ : (∙Susp (typ B) →∙ X , β) →∙ (∙Susp (typ B) →∙ X ∙)
    fst (fst ξ (γ , γ∙)) north = β .fst north
    fst (fst ξ (γ , γ∙)) south = γ north
    fst (fst ξ (γ , γ∙)) (merid b i) = ξ-path (γ , γ∙) b i
    snd (fst ξ (γ , γ∙)) = β .snd
    fst (snd ξ i) north = β .snd i
    fst (snd ξ i) south = β .snd i
    fst (snd ξ i) (merid b j) =
      hcomp (λ k → λ { (i = i0) → ξ-path-id b (~ k) j
                     ; (i = i1) → pt X
                     ; (j = i0) → β .snd i
                     ; (j = i1) → β .snd i }) (β .snd i)
    snd (snd ξ i) j = β .snd (i ∨ j)

    -- composition with ξ
    ζ : (A →∙ (∙Susp (typ B) →∙ X , β))
        → (A →∙ (∙Susp (typ B) →∙ X ∙))
    ζ γ = ξ ∘∙ γ

    -- Whitehead product with β
    ρ-path : (α : ∙Susp (typ A) →∙ X) (a : typ A) (b : typ B)
             → Path (typ X) (β .fst north) (α .fst north)
    ρ-path (α , α∙) a b = (cong (β .fst) (σ B b))
      ∙∙ (β .snd ∙ sym α∙) ∙∙ (cong α (σ A a))

    ρ : (∙Susp (typ A) →∙ X) → (∙join A B →∙ X)
    fst (ρ (α , α∙)) (inl a) = β .fst north
    fst (ρ (α , α∙)) (inr b) = α north
    fst (ρ (α , α∙)) (push a b i) = ρ-path (α , α∙) a b i
    snd (ρ (α , α∙)) = β .snd

{-
    thm-inl : (α : ∙Susp (typ A) →∙ X) (a : typ A) → β .fst north ≡ pt X
    thm-inl (α , α∙) a = (β .snd ∙ sym α∙) ∙∙ (λ j → α (σ A a j)) ∙∙ α∙

    thm-inl-pt : (α : ∙Susp (typ A) →∙ X) → thm-inl α (pt A) ≡ β .snd
    thm-inl-pt (α , α∙) =
      thm-inl (α , α∙) (pt A)
        ≡⟨ cong (λ q → (β .snd ∙ sym α∙) ∙∙ q ∙∙ α∙) (λ i j → α (σ-pt A i j)) ⟩
      (β .snd ∙ sym α∙) ∙∙ refl ∙∙ α∙
        ≡⟨ doubleCompPath-elim' (β .snd ∙ sym α∙) refl α∙ ⟩
      (β .snd ∙ sym α∙) ∙ (refl ∙ α∙)
        ≡⟨ cong (λ q → (β .snd ∙ sym α∙) ∙ q) (sym (lUnit α∙)) ⟩
      (β .snd ∙ sym α∙) ∙ α∙
        ≡⟨ sym (assoc (β .snd) (sym α∙) α∙) ⟩
      β .snd ∙ (sym α∙ ∙ α∙)
        ≡⟨ cong (λ q → β .snd ∙ q) (lCancel α∙) ⟩
      β .snd ∙ refl
        ≡⟨ sym (rUnit (β .snd)) ⟩
      β .snd ∎
-}

    thm-inr : (α : ∙Susp (typ A) →∙ X) (b : typ B) → α .fst north ≡ pt X
    thm-inr (α , α∙) b = (α∙ ∙ sym (β .snd))
      ∙∙ sym (cong (β .fst) (σ B b)) ∙∙ β .snd

    lemma : (α : ∙Susp (typ A) →∙ X)(a : typ A)(b : typ B)
      → refl ∙ ρ-path α a b ∙ thm-inr α b ≡ φ-path (fst (ξ ∘∙ ∂ α)) a b
    lemma (α , α∙) a b =
      refl ∙ ρ-path (α , α∙) a b ∙ thm-inr (α , α∙) b
      ≡⟨ sym (lUnit (ρ-path (α , α∙) a b ∙ thm-inr (α , α∙) b)) ⟩
      ρ-path (α , α∙) a b ∙ thm-inr (α , α∙) b
      ≡⟨ refl ⟩
      ((cong (β .fst) (σ B b)) ∙∙ (β .snd ∙ sym α∙) ∙∙ (cong α (σ A a)))
      ∙ ((α∙ ∙ sym (β .snd)) ∙∙ sym (cong (β .fst) (σ B b)) ∙∙ β .snd)
      ≡⟨ {!!} ⟩
      (cong (h a .fst) (σ B b)) ∙ h a .snd
      ≡⟨ {!!} ⟩
      φ-path h a b
      ∎
      where
        h : typ A → (∙Susp (typ B) →∙ X)
        h = fst (ξ ∘∙ ∂ (α , α∙))

    thm : (α : ∙Susp (typ A) →∙ X) → ρ α ≡ φ (ζ (∂ α))
    fst (thm (α , α∙) i) (inl a) = β .fst north
    fst (thm (α , α∙) i) (inr b) = thm-inr (α , α∙) b i
    fst (thm (α , α∙) i) (push a b j) = compPathL→PathP {p = λ k → β .fst north}
                                        (lemma (α , α∙) a b) i j
    snd (thm (α , α∙) i) = β .snd
