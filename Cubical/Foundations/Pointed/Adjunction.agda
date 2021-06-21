{-# OPTIONS --safe #-}

module Cubical.Foundations.Pointed.Adjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed

{-
  This module contains a definition
  of a (heterogeneous) wild adjunction of pointed types
  and a construction of the transposing isomorphism
  given this data.

  To give a polymorphic result we duplicate many fields,
  but each functor is assumed to preserve levels
  (which is often the case in practice),
  however, we could make it even more polymorphic
  with separate pairs of levels for the domains and codomains
  of the adjunction.
-}

private
  variable
    ℓˡ ℓʳ : Level

record PtdAdjunction
  (Fˡ : Pointed ℓˡ → Pointed ℓˡ) (Fʳ : Pointed ℓʳ → Pointed ℓʳ)
  (F→ˡ : {A A' : Pointed ℓˡ} → (A →∙ A') → (Fˡ A →∙ Fˡ A'))
  (F→ʳ : {A : Pointed ℓˡ}{A' : Pointed ℓʳ} → (A →∙ A') → (Fˡ A →∙ Fʳ A'))
  (Gˡ : Pointed ℓˡ → Pointed ℓˡ) (Gʳ : Pointed ℓʳ → Pointed ℓʳ)
  (G→ˡ : {B : Pointed ℓˡ}{B' : Pointed ℓʳ} → (B →∙ B') → (Gˡ B →∙ Gʳ B'))
  (G→ʳ : {B B' : Pointed ℓʳ} → (B →∙ B') → (Gʳ B →∙ Gʳ B'))
  : Type (ℓ-suc (ℓ-max ℓˡ ℓʳ)) where
  field
    -- unit
    ηˡ : (A : Pointed ℓˡ) → (A →∙ Gˡ (Fˡ A))
    ηʳ : (A : Pointed ℓʳ) → (A →∙ Gʳ (Fʳ A))
    η→ : {A : Pointed ℓˡ}{A' : Pointed ℓʳ}(f : A →∙ A') → G→ˡ (F→ʳ f) ∘∙ ηˡ A ≡ ηʳ A' ∘∙ f
    -- counit
    εˡ : (B : Pointed ℓˡ) → (Fˡ (Gˡ B) →∙ B)
    εʳ : (B : Pointed ℓʳ) → (Fʳ (Gʳ B) →∙ B)
    ε→ : {B : Pointed ℓˡ}{B' : Pointed ℓʳ}(g : B →∙ B') → εʳ B' ∘∙ F→ʳ (G→ˡ g) ≡ g ∘∙ εˡ B
    -- triangle identities
    εF-Fη : (A : Pointed ℓˡ) → εˡ (Fˡ A) ∘∙ F→ˡ (ηˡ A) ≡ id∙ (Fˡ A)
    Gε-ηG : (B : Pointed ℓʳ) → G→ʳ (εʳ B) ∘∙ ηʳ (Gʳ B) ≡ id∙ (Gʳ B)

-- to give the transposing isomorphism we need in addition
-- that F→ and G→ preserve compositions (but not nec. identities)

module _
  (Fˡ : Pointed ℓˡ → Pointed ℓˡ) (Fʳ : Pointed ℓʳ → Pointed ℓʳ)
  (F→ˡ : {A A' : Pointed ℓˡ} → (A →∙ A') → (Fˡ A →∙ Fˡ A'))
  (F→ʳ : {A : Pointed ℓˡ}{A' : Pointed ℓʳ} → (A →∙ A') → (Fˡ A →∙ Fʳ A'))
  (F→∘∙ : {A A' : Pointed ℓˡ}{A'' : Pointed ℓʳ}(f' : A' →∙ A'')(f : A →∙ A')
          → F→ʳ (f' ∘∙ f) ≡ F→ʳ f' ∘∙ F→ˡ f)
  (Gˡ : Pointed ℓˡ → Pointed ℓˡ) (Gʳ : Pointed ℓʳ → Pointed ℓʳ)
  (G→ˡ : {B : Pointed ℓˡ}{B' : Pointed ℓʳ} → (B →∙ B') → (Gˡ B →∙ Gʳ B'))
  (G→ʳ : {B B' : Pointed ℓʳ} → (B →∙ B') → (Gʳ B →∙ Gʳ B'))
  (G→∘∙ : {B : Pointed ℓˡ}{B' B'' : Pointed ℓʳ}(g' : B' →∙ B'')(g : B →∙ B')
          → G→ˡ (g' ∘∙ g) ≡ G→ʳ g' ∘∙ G→ˡ g)
  (F⊣G : PtdAdjunction Fˡ Fʳ F→ˡ F→ʳ Gˡ Gʳ G→ˡ G→ʳ)
  where

  open PtdAdjunction F⊣G

  PtdAdjunctionIso : (A : Pointed ℓˡ)(B : Pointed ℓʳ)
    → Iso (Fˡ A →∙ B) (A →∙ Gʳ B)
  Iso.fun (PtdAdjunctionIso A B) g = G→ˡ g ∘∙ ηˡ A
  Iso.inv (PtdAdjunctionIso A B) f = εʳ B ∘∙ F→ʳ f
  Iso.rightInv (PtdAdjunctionIso A B) f =
    G→ˡ (εʳ B ∘∙ F→ʳ f) ∘∙ ηˡ A
      ≡⟨ cong (λ h → h ∘∙ ηˡ A) (G→∘∙ (εʳ B) (F→ʳ f) ) ⟩
    (G→ʳ (εʳ B) ∘∙ G→ˡ (F→ʳ f)) ∘∙ ηˡ A
      ≡⟨ ∘∙-assoc (G→ʳ (εʳ B)) (G→ˡ (F→ʳ f)) (ηˡ A) ⟩
    G→ʳ (εʳ B) ∘∙ (G→ˡ (F→ʳ f) ∘∙ ηˡ A)
      ≡⟨ cong (λ h → G→ʳ (εʳ B) ∘∙ h) (η→ f) ⟩
    G→ʳ (εʳ B) ∘∙ (ηʳ (Gʳ B) ∘∙ f)
      ≡⟨ sym (∘∙-assoc (G→ʳ (εʳ B)) (ηʳ (Gʳ B)) f) ⟩
    (G→ʳ (εʳ B) ∘∙ ηʳ (Gʳ B)) ∘∙ f
      ≡⟨ cong (λ h → h ∘∙ f) (Gε-ηG B) ⟩
    id∙ (Gʳ B) ∘∙ f
      ≡⟨ ∘∙-idʳ f ⟩
    f ∎
  Iso.leftInv (PtdAdjunctionIso A B) g =
    εʳ B ∘∙ F→ʳ (G→ˡ g ∘∙ ηˡ A)
      ≡⟨ cong (λ h → εʳ B ∘∙ h) (F→∘∙ (G→ˡ g) (ηˡ A)) ⟩
    εʳ B ∘∙ (F→ʳ (G→ˡ g) ∘∙ F→ˡ (ηˡ A))
      ≡⟨ sym (∘∙-assoc (εʳ B) (F→ʳ (G→ˡ g)) (F→ˡ (ηˡ A))) ⟩
    (εʳ B ∘∙ (F→ʳ (G→ˡ g))) ∘∙ F→ˡ (ηˡ A)
      ≡⟨ cong (λ h → h ∘∙ F→ˡ (ηˡ A)) (ε→ g) ⟩
    (g ∘∙ εˡ (Fˡ A)) ∘∙ F→ˡ (ηˡ A)
      ≡⟨ ∘∙-assoc g (εˡ (Fˡ A)) (F→ˡ (ηˡ A)) ⟩
    g ∘∙ (εˡ (Fˡ A) ∘∙ F→ˡ (ηˡ A))
      ≡⟨ cong (λ h → g ∘∙ h) (εF-Fη A) ⟩
    g ∘∙ id∙ (Fˡ A)
      ≡⟨ ∘∙-idˡ g ⟩
    g ∎
