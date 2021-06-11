-- some equivalences concerning smash join and susp

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.SmashJoinSusp where

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
    ℓ ℓA ℓA' ℓB ℓX ℓX' : Level

σ : (A : Pointed ℓA) → (typ A) → typ (Ω (∙Susp (typ A)))
σ A a = merid a ∙ sym (merid (pt A))

σ-pt : (A : Pointed ℓA) → σ A (pt A) ≡ refl
σ-pt A = rCancel (merid (pt A))

∙join : ∀ {ℓA ℓB} → Pointed ℓA → Pointed ℓB → Pointed (ℓ-max ℓA ℓB)
fst (∙join A B) = join (typ A) (typ B)
snd (∙join A B) = inl (pt A)

-- an equivalence between the join and smash with a suspension
module _ {ℓA ℓB} (A : Pointed ℓA) (B : Pointed ℓB) where

  to-path : (a : typ A)(b : typ B)
    → Path (Smash A (∙Susp (typ B))) (proj a north) basel
  to-path a b = (λ i → proj a (merid b i)) ∙∙
    (λ i → proj a (merid (pt B) (~ i))) ∙∙ gluel a

  to : ∙join A B →∙ SmashPtProj A (∙Susp (typ B))
  fst to (inl a) = proj a north
  fst to (inr b) = basel
  fst to (push a b i) = to-path a b i
  snd to i = proj (pt A) north

  from-path : (a : typ A)(b : typ B)
    → Path (join (typ A) (typ B)) (inl a) (inl (pt A))
  from-path a b = push a b ∙ sym (push (pt A) b)

  from-path-pt : (b : typ B) → from-path (pt A) b ≡ refl
  from-path-pt b = rCancel (push (pt A) b)

  from : SmashPtProj A (∙Susp (typ B)) →∙ ∙join A B
  fst from basel = inr (pt B)
  fst from baser = inl (pt A)
  fst from (proj a north) = inl a
  fst from (proj a south) = inl (pt A)
  fst from (proj a (merid b i)) = from-path a b i
  fst from (gluel a i) = push a (pt B) i
  fst from (gluer north i) = inl (pt A)
  fst from (gluer south i) = inl (pt A)
  fst from (gluer (merid b j) i) = from-path-pt b i j
  snd from i = inl (pt A)

  from-to : from ∘∙ to ≡ idfun∙ (∙join A B)
  fst (from-to i) (inl a) = inl a
  fst (from-to i) (inr b) = (sym (push (pt A) (pt B)) ∙ push (pt A) b) i
  fst (from-to i) (push a b j) = {!!} -- ✓
  snd (from-to i) = sym (rUnit refl) i

  to-from-path : (a : typ A)
    → Path (Smash A (∙Susp (typ B))) (proj (pt A) north) (proj a south)
  to-from-path a = gluel (pt A) ∙∙ sym (gluel a)
                                ∙∙ λ i → proj a (merid (pt B) i)

  to-from : to ∘∙ from ≡ idfun∙ (SmashPtProj A (∙Susp (typ B)))
  fst (to-from i) basel = basel
  fst (to-from i) baser = gluer north i
  fst (to-from i) (proj a north) = proj a north
  fst (to-from i) (proj a south) = to-from-path a i
  fst (to-from i) (proj a (merid b j)) = {!!}
  fst (to-from i) (gluel a j) = {!!}
  fst (to-from i) (gluer north j) = gluer north (i ∧ j)
  fst (to-from i) (gluer south j) = {!!}
  fst (to-from i) (gluer (merid b k) j) = {!!}
  snd (to-from i) j = sym (rUnit refl) i j


-- adjunction between join and mapping from suspension
module _ (B : Pointed ℓB) where

  join-mapₗ : {A : Pointed ℓA} {A' : Pointed ℓA'}
    → (A →∙ A') → (∙join A B →∙ ∙join A' B)
  fst (join-mapₗ f) (inl a) = inl (fst f a)
  fst (join-mapₗ f) (inr b) = inr b
  fst (join-mapₗ f) (push a b i) = push (fst f a) b i
  snd (join-mapₗ f) i = inl (snd f i)

  spmap-mapₗ : {X : Pointed ℓX} {X' : Pointed ℓX'}
    → (X →∙ X') → ((∙Susp (typ B) →∙ X ∙) →∙ (∙Susp (typ B) →∙ X' ∙))
  fst (spmap-mapₗ f) g = f ∘∙ g
  fst (snd (spmap-mapₗ f) i) _ = snd f i
  snd (snd (spmap-mapₗ f) i) j =
    hcomp (λ k → λ { (i = i0) → doubleCompPath-filler refl refl (snd f) k j
                   ; (i = i1) → snd f i1
                   ; (j = i0) → snd f i
                   ; (j = i1) → snd f (i ∨ k) })
          (snd f i)

  -- unit
  sspm-unit-sq : (A : Pointed ℓA) (b : typ B)
    → Square {A = join (typ A) (typ B)}
             (push (pt A) b ∙ sym (push (pt A) b)) refl refl refl
  sspm-unit-sq A b i j = rCancel (push (pt A) b) i j

  sspm-unit : (A : Pointed ℓA) → A →∙ (∙Susp (typ B) →∙ ∙join A B ∙)
  fst (fst (sspm-unit A) a) north = inl a
  fst (fst (sspm-unit A) a) south = inl (pt A)
  fst (fst (sspm-unit A) a) (merid b i) = (push a b ∙ sym (push (pt A) b)) i
  snd (fst (sspm-unit A) a) = push a (pt B) ∙ sym (push (pt A) (pt B))
  fst (snd (sspm-unit A) i) north = inl (pt A)
  fst (snd (sspm-unit A) i) south = inl (pt A)
  fst (snd (sspm-unit A) i) (merid b j) = sspm-unit-sq A b i j
  snd (snd (sspm-unit A) i) j = sspm-unit-sq A (pt B) i j

  sspm-unit-sq-nat : {A : Pointed ℓA}{A' : Pointed ℓA'}(f : A →∙ A')
    (b : typ B) → {!!}
  sspm-unit-sq-nat f b = {!!}

  sspm-unit-nat : {A : Pointed ℓA}{A' : Pointed ℓA'}(f : A →∙ A')
    → spmap-mapₗ (join-mapₗ f) ∘∙ sspm-unit A ≡ sspm-unit A' ∘∙ f
  fst (fst (sspm-unit-nat f i) a) north = inl (fst f a)
  fst (fst (sspm-unit-nat f i) a) south = inl (snd f i)
  fst (fst (sspm-unit-nat f i) a) (merid b j) = {!!}
  snd (fst (sspm-unit-nat f i) a) j = {!!}
  fst (snd (sspm-unit-nat f i) j) = {!!}
  snd (snd (sspm-unit-nat f i) j) = {!!}

  sspm-counit : (X : Pointed ℓX) → (∙join (∙Susp (typ B) →∙ X ∙) B) →∙ X
  fst (sspm-counit X) (inl (f , f∙)) = pt X
  fst (sspm-counit X) (inr b) = pt X
  fst (sspm-counit X) (push (f , f∙) b i) = (sym f∙ ∙∙ cong f (σ B b) ∙∙ f∙) i
  snd (sspm-counit X) i = pt X

  sspm-counit-nat : {X : Pointed ℓX}{X' : Pointed ℓX'}(f : X →∙ X')
    → sspm-counit X' ∘∙ join-mapₗ (spmap-mapₗ f) ≡ f ∘∙ sspm-counit X
  fst (sspm-counit-nat f i) (inl a) = snd f (~ i)
  fst (sspm-counit-nat f i) (inr b) = snd f (~ i)
  fst (sspm-counit-nat f i) (push g b j) =
    hcomp (λ k → λ { (i = i0) → doubleCompPath-filler
      (sym (cong (fst f) (snd g) ∙ snd f))
      (λ u → fst f (fst g (σ B b u)))
      (cong (fst f) (snd g) ∙ snd f) k j
                   ; (i = i1) → cong-∙∙ (fst f)
      (sym (snd g)) (cong (fst g) (σ B b)) (snd g) (~ k) j
                   ; (j = i0) → sq i k
                   ; (j = i1) → sq i k })
          (doubleCompPath-filler (λ k → fst f (snd g (~ k)))
                                 (λ k → fst f (fst g (σ B b k)))
                                 (λ k → fst f (snd g k)) i j)
    where
      sq : Square (cong (fst f) (snd g) ∙ snd f) refl
                  (cong (fst f) (snd g)) (sym (snd f))
      sq i j =
        hcomp (λ k → λ { (i = i0) → doubleCompPath-filler refl (cong (fst f) (snd g)) (snd f) k j
                       ; (i = i1) → fst f (snd g i1)
                       ; (j = i0) → fst f (snd g i)
                       ; (j = i1) → snd f ((~ i) ∧ k) }) (fst f (snd g (i ∨ j)))

  snd (sspm-counit-nat f i) j =
    hcomp (λ k → λ { (i = i0) → doubleCompPath-filler {x = snd f i1}
                                refl refl refl k j
                   ; (i = i1) → doubleCompPath-filler refl refl (snd f) k j
                   ; (j = i0) → snd f (~ i)
                   ; (j = i1) → snd f ((~ i) ∨ k) })
          (snd f (~ i))

  sspm-unit-counit : (A : Pointed ℓA)
    → sspm-counit (∙join A B) ∘∙ join-mapₗ (sspm-unit A) ≡ idfun∙ (∙join A B)
  fst (sspm-unit-counit A i) (inl a) =
    ((λ k → push (pt A) (pt B) k) ∙ λ k → push a (pt B) (~ k)) i
  fst (sspm-unit-counit A i) (inr b) = push (pt A) b i
  fst (sspm-unit-counit A i) (push a b j) = {!!}
  snd (sspm-unit-counit A i) j =
    hcomp (λ k → λ { (i = i0) → doubleCompPath-filler {x = inl (pt A)}
                                                      refl refl refl k j
                   ; (i = i1) → p ((~ j) ∧ (~ k))
                   ; (j = i0) → doubleCompPath-filler refl p (sym p) k i
                   ; (j = i1) → inl (pt A) }) (p (i ∧ (~ j)))
    where
      p : Path (join (typ A) (typ B)) (inl (pt A)) (inr (pt B))
      p = push (pt A) (pt B)

  sspm-counit-unit : (X : Pointed ℓX)
    → spmap-mapₗ (sspm-counit X) ∘∙ sspm-unit (∙Susp (typ B) →∙ X ∙)
    ≡ idfun∙ (∙Susp (typ B) →∙ X ∙)
  fst (fst (sspm-counit-unit X i) (f , f∙)) north = f∙ (~ i)
  fst (fst (sspm-counit-unit X i) (f , f∙)) south =
    (sym f∙ ∙ cong f (merid (pt B))) i
  fst (fst (sspm-counit-unit X i) (f , f∙)) (merid b j) = {!!}
  snd (fst (sspm-counit-unit X i) (f , f∙)) j = {!!}
  fst (snd (sspm-counit-unit X i) j) north = {!!}
  fst (snd (sspm-counit-unit X i) j) south = {!!}
  fst (snd (sspm-counit-unit X i) j) (merid b k) = {!!}
  snd (snd (sspm-counit-unit X i) j) = {!!}

  -- check that the transposing map from the adjunction
  -- equals the map φ in the paper
  module _ (A : Pointed ℓA)(X : Pointed ℓX) where

    transpose : (A →∙ (∙Susp (typ B) →∙ X ∙)) → (∙join A B →∙ X)
    transpose h = sspm-counit X ∘∙ join-mapₗ h

    ψ-path : (h : typ A → (∙Susp (typ B) →∙ X)) (a : typ A) (b : typ B)
      → Path (typ X) (pt X) (pt X)
    ψ-path h a b = sym (h a .snd) ∙∙ (cong (h a .fst) (σ B b )) ∙∙ h a .snd

    ψ : (A →∙ (∙Susp (typ B) →∙ X ∙)) → (∙join A B →∙ X)
    fst (ψ (h , h∙)) (inl a) = pt X
    fst (ψ (h , h∙)) (inr b) = pt X
    fst (ψ (h , h∙)) (push a b i) = ψ-path h a b i
    snd (ψ (h , h∙)) = refl

    lemma : transpose ≡ ψ
    fst (lemma i (h , h∙)) (inl a) = pt X
    fst (lemma i (h , h∙)) (inr b) = pt X
    fst (lemma i (h , h∙)) (push a b j) = ψ-path h a b j
    snd (lemma i (h , h∙)) j =
      doubleCompPath-filler {x = pt X} refl refl refl (~ i) j

    φ-path : (h : typ A → (∙Susp (typ B) →∙ X)) (a : typ A) (b : typ B)
      → Path (typ X) (h a .fst north) (pt X)
    φ-path h a b = (cong (h a .fst) (σ B b )) ∙ h a .snd

    φ : (A →∙ (∙Susp (typ B) →∙ X ∙)) → (∙join A B →∙ X)
    fst (φ (h , h∙)) (inl a) = h a .fst north
    fst (φ (h , h∙)) (inr b) = pt X
    fst (φ (h , h∙)) (push a b i) = φ-path h a b i
    snd (φ (h , h∙)) = h (pt A) .snd

    agree : φ ≡ ψ
    fst (agree i (h , h∙)) (inl a) = h a .snd i
    fst (agree i (h , h∙)) (inr b) = pt X
    fst (agree i (h , h∙)) (push a b j) =
      hcomp (λ k → λ { (i = i0) → doubleCompPath-filler refl
                                  (cong (h a .fst) (σ B b)) (h a .snd) k j
                     ; (i = i1) → doubleCompPath-filler (sym (h a .snd))
                                  (cong (h a .fst) (σ B b)) (h a .snd) k j
                     ; (j = i0) → h a .snd (i ∧ k)
                     ; (j = i1) → h a .snd k }) (h a .fst (σ B b j))
    snd (agree i (h , h∙)) j = h (pt A) .snd (i ∨ j)
