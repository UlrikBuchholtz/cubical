{-# OPTIONS --safe #-}
module Cubical.HITs.Susp.LoopAdjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Pointed.Adjunction
open import Cubical.Foundations.SIP

open import Cubical.Structures.Pointed
open import Cubical.HITs.Susp.Base
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓA ℓA' ℓA'' ℓB ℓB' ℓB'' : Level

∙Susp→ : {A : Type ℓA} {A' : Type ℓA'} (f : A → A') → (∙Susp A →∙ ∙Susp A')
fst (∙Susp→ f) = suspFun f
snd (∙Susp→ f) = refl

∙Susp→∘∙ : {A : Type ℓA} {A' : Type ℓA'} {A'' : Type ℓA''}
           → (f' : A' → A'') → (f : A → A')
           → ∙Susp→ (λ x → f' (f x)) ≡ ∙Susp→ f' ∘∙ ∙Susp→ f
fst (∙Susp→∘∙ f' f i) north = north
fst (∙Susp→∘∙ f' f i) south = south
fst (∙Susp→∘∙ f' f i) (merid a j) = merid (f' (f a)) j
snd (∙Susp→∘∙ f' f i) = rUnit refl i

{-
  The adjunction ∙Susp ⊣ Ω on pointed types
-}

sl-unit : (A : Pointed ℓA) → A →∙ Ω (∙Susp (typ A))
fst (sl-unit A) a = merid a ∙ sym (merid (pt A))
snd (sl-unit A) = rCancel (merid (pt A))

sl-unit-nat : {A : Pointed ℓA}{A' : Pointed ℓA'}(f : A →∙ A')
    → Ω→ (∙Susp→ (fst f)) ∘∙ sl-unit A ≡ sl-unit A' ∘∙ f
sl-unit-nat {A = A} {A' = A'} f = →∙Homogeneous≡ (isHomogeneousPath (Susp (typ A')) refl)
  (funExt lemma)
  where
    g = suspFun (fst f)

    lemma : (a : typ A) → fst (Ω→ (g , refl) ∘∙ sl-unit A) a ≡ fst (sl-unit A' ∘∙ f) a
    lemma a =
      refl ∙∙ cong g (merid a ∙ sym (merid (pt A))) ∙∙ refl
        ≡⟨ sym (rUnit (cong g (merid a ∙ sym (merid (pt A))))) ⟩
      cong g (merid a ∙ sym (merid (pt A)))
        ≡⟨ cong-∙ g (merid a) (sym (merid (pt A))) ⟩
      merid (fst f a) ∙ sym (merid (fst f (pt A)))
        ≡⟨ cong (λ y → merid (fst f a) ∙ sym (merid y)) (snd f) ⟩
      merid (fst f a) ∙ sym (merid (pt A'))
        ∎

sl-counit : (B : Pointed ℓB) → ∙Susp (typ (Ω B)) →∙ B
fst (sl-counit B) north = pt B
fst (sl-counit B) south = pt B
fst (sl-counit B) (merid p i) = p i
snd (sl-counit B) = refl

sl-counit-nat : {B : Pointed ℓB}{B' : Pointed ℓB'}(f : B →∙ B')
    → sl-counit B' ∘∙ ∙Susp→ (Ω→ f .fst) ≡ f ∘∙ sl-counit B
fst (sl-counit-nat f i) north = snd f (~ i)
fst (sl-counit-nat f i) south = snd f (~ i)
fst (sl-counit-nat f i) (merid p j) = doubleCompPath-filler
  (sym (snd f)) (cong (fst f) p) (snd f) (~ i) j
snd (sl-counit-nat f i) j = hcomp
  (λ k → λ { (i = i0) → doubleCompPath-filler {x = snd f i1} refl refl refl k j
             ; (i = i1) → doubleCompPath-filler refl refl (snd f) k j
             ; (j = i0) → snd f (~ i)
             ; (j = i1) → snd f ((~ i) ∨ k) }) (snd f (~ i))

sl-unit-counit : (A : Pointed ℓA)
  → sl-counit (∙Susp (typ A)) ∘∙ ∙Susp→ (sl-unit A .fst) ≡ idfun∙ (∙Susp (typ A))
fst (sl-unit-counit A i) north = north
fst (sl-unit-counit A i) south = merid (pt A) i
fst (sl-unit-counit A i) (merid a j) = doubleCompPath-filler
  refl (merid a) (sym (merid (pt A))) (~ i) j
snd (sl-unit-counit A i) j = doubleCompPath-filler {x = north} refl refl refl (~ i) j

sl-counit-unit : (B : Pointed ℓB)
  → Ω→ (sl-counit B) ∘∙ sl-unit (Ω B) ≡ idfun∙ (Ω B)
sl-counit-unit B = →∙Homogeneous≡ (isHomogeneousPath (typ B) refl) (funExt lemma)
  where
    f = fst (sl-counit B)

    lemma : (p : typ (Ω B)) → fst (Ω→ (sl-counit B) ∘∙ sl-unit (Ω B)) p ≡ p
    lemma p =
      refl ∙∙ cong f (merid p ∙ sym (merid refl)) ∙∙ refl
        ≡⟨ sym (rUnit (cong f (merid p ∙ sym (merid refl)))) ⟩
      cong f (merid p ∙ sym (merid refl))
        ≡⟨ cong-∙ f (merid p) (sym (merid refl)) ⟩
      p ∙ refl
        ≡⟨ sym (rUnit p) ⟩
      p ∎

module _ where
  private
    F : {ℓ : Level} → Pointed ℓ → Pointed ℓ
    F X = ∙Susp (typ X)

    F→ : {ℓ ℓ' : Level}{A : Pointed ℓ}{A' : Pointed ℓ'} → (A →∙ A') → (F A →∙ F A')
    F→ f = ∙Susp→ (fst f)

    F→∘∙ : {ℓ ℓ' ℓ'' : Level}{A : Pointed ℓ}{A' : Pointed ℓ'}{A'' : Pointed ℓ''}
           (f' : A' →∙ A'')(f : A →∙ A') → F→ (f' ∘∙ f) ≡ F→ f' ∘∙ F→ f
    F→∘∙ f' f = ∙Susp→∘∙ (fst f') (fst f)

  LoopSuspIso : (A : Pointed ℓA) (B : Pointed ℓB) → Iso (A →∙ Ω B) (∙Susp (typ A) →∙ B)
  LoopSuspIso A B = invIso (PtdAdjunctionIso F F F→ F→ F→∘∙ Ω Ω Ω→ Ω→ Ω→∘∙ Σ⊣Ω A B)
    where
      Σ⊣Ω : PtdAdjunction F F F→ F→ Ω Ω Ω→ Ω→
      PtdAdjunction.ηˡ Σ⊣Ω = sl-unit
      PtdAdjunction.ηʳ Σ⊣Ω = sl-unit
      PtdAdjunction.η→ Σ⊣Ω = sl-unit-nat
      PtdAdjunction.εˡ Σ⊣Ω = sl-counit
      PtdAdjunction.εʳ Σ⊣Ω = sl-counit
      PtdAdjunction.ε→ Σ⊣Ω = sl-counit-nat
      PtdAdjunction.εF-Fη Σ⊣Ω = sl-unit-counit
      PtdAdjunction.Gε-ηG Σ⊣Ω = sl-counit-unit

  LoopSuspPEquiv : (A : Pointed ℓA) (B : Pointed ℓB)
    → (A →∙ Ω B ∙) ≃[ PointedEquivStr ] (∙Susp (typ A) →∙ B ∙)
  fst (LoopSuspPEquiv A B) = isoToEquiv (LoopSuspIso A B)
  fst (snd (LoopSuspPEquiv A B) i) north = pt B
  fst (snd (LoopSuspPEquiv A B) i) south = pt B
  fst (snd (LoopSuspPEquiv A B) i) (merid a j) = pt B
  snd (snd (LoopSuspPEquiv A B) i) j = doubleCompPath-filler {x = pt B} refl refl refl (~ i) j

  LoopSuspPath : (A : Pointed ℓA) (B : Pointed ℓB) → (A →∙ Ω B ∙) ≡ (∙Susp (typ A) →∙ B ∙)
  LoopSuspPath A B = pointed-sip _ _ (LoopSuspPEquiv A B)
