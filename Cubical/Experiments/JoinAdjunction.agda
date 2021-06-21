-- adjunction between join and mapping from suspension
-- (special case of smash and pmap adjunction)

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.JoinAdjunction where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Pointed.Adjunction

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.HomotopyGroup

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Susp
open import Cubical.HITs.Susp.LoopAdjunction
open import Cubical.HITs.Join
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

  -- homogeneity
  spmap-homogeneous : (X : Pointed ℓX) → isHomogeneous (∙Susp (typ B) →∙ X ∙)
  spmap-homogeneous X = subst (λ Z → isHomogeneous Z) (LoopSuspPath B X)
    (isHomogeneous→∙ (isHomogeneousPath (typ X) refl))

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

  sspm-unit-nat : {A : Pointed ℓA}{A' : Pointed ℓA'}(f : A →∙ A')
    → spmap-mapₗ (join-mapₗ f) ∘∙ sspm-unit A ≡ sspm-unit A' ∘∙ f
  sspm-unit-nat {A = A} {A' = A'} f = →∙Homogeneous≡ (spmap-homogeneous (∙join A' B)) lemma
    where
      lemma : fst (spmap-mapₗ (join-mapₗ f) ∘∙ sspm-unit A) ≡ fst (sspm-unit A' ∘∙ f)
      fst (lemma i a) north = inl (fst f a)
      fst (lemma i a) south = inl (snd f i)
      fst (lemma i a) (merid b j) = hcomp
        (λ k → λ { (i = i0) → fst (join-mapₗ f) (doubleCompPath-filler
                                  refl (push a b) (sym (push (pt A) b)) k j)
                 ; (i = i1) → doubleCompPath-filler refl (push (fst f a) b)
                                                    (sym (push (pt A') b)) k j
                 ; (j = i0) → inl (fst f a)
                 ; (j = i1) → push (snd f i) b (~ k) }) (push (fst f a) b j)
      snd (lemma i a) j = hcomp
        (λ k → λ { (i = i0) → doubleCompPath-filler refl
                      (cong (join-mapₗ f .fst) (push a (pt B) ∙ sym (push (pt A) (pt B))))
                      (cong inl (snd f)) k j
                 ; (i = i1) → doubleCompPath-filler refl (push (fst f a) (pt B))
                      (sym (push (pt A') (pt B))) k j
                 ; (j = i0) → inl (fst f a)
                 ; (j = i1) → hcomp
                      (λ j → λ { (i = i0) → inl (snd f (~ j ∨ k))
                               ; (i = i1) → push (pt A') (pt B) (~ k)
                               ; (k = i0) → push (snd f (~ j)) (pt B) i
                               ; (k = i1) → inl (pt A') }) (push (pt A') (pt B) (i ∧ (~ k))) })
        (fst (join-mapₗ f) (doubleCompPath-filler refl (push a (pt B))
                                                  (sym (push (pt A) (pt B))) (~ i) j))
        where
          p = push (fst f a) (pt B)
          q = push (fst f (pt A)) (pt B)

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
  fst (sspm-unit-counit A i) (push a b j) = hcomp
    (λ k → λ { (i = i0) → doubleCompPath-filler (sym (snd f)) (cong (fst f) (σ B b)) (snd f) k j
             ; (i = i1) → doubleCompPath-filler refl (push a b) (sym (push (pt A) b)) (~ k) j
             ; (j = i0) → slideSquare (symDistr (push (pt A) (pt B)) (sym (push a (pt B)))) (~ i) k
             ; (j = i1) → invSides-filler (push (pt A) b) (sym (snd f)) (~ i) k})
             (fst f (doubleCompPath-filler refl (merid b) (sym (merid (pt B))) (~ i) j))
    where
      f = fst (sspm-unit A) a
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
  sspm-counit-unit X = →∙Homogeneous≡ (spmap-homogeneous X) lemma
    where
      c : ∙Susp (typ B) →∙ X
      c = pt (∙Susp (typ B) →∙ X ∙)

      lemma : fst (spmap-mapₗ (sspm-counit X) ∘∙ sspm-unit (∙Susp (typ B) →∙ X ∙))
            ≡ idfun (∙Susp (typ B) →∙ X)
      fst (lemma i f) north = snd f (~ i)
      fst (lemma i f) south = (sym (snd f) ∙ cong (fst f) (merid (pt B))) i
      fst (lemma i f) (merid b j) = hcomp
        (λ k → λ { (i = i0) → fst (sspm-counit X) (doubleCompPath-filler refl
                                  (push f b) (sym (push c b)) k j)
                 ; (i = i1) → fst f (doubleCompPath-filler refl (merid b)
                                  (sym (merid (pt B))) (~ k) j)
                 ; (j = i0) → snd f (~ i)
                 ; (j = i1) → hcomp
                   (λ j → λ { (i = i0) → doubleCompPath-filler {x = pt X} refl refl refl j k
                            ; (i = i1) → fst f (merid (pt B) (j ∧ k))
                            ; (k = i0) → snd f (~ i)
                            ; (k = i1) → doubleCompPath-filler refl (sym (snd f)) (cong (fst f)
                                 (merid (pt B))) j i })
                   (snd f (~ i)) })
        (doubleCompPath-filler (sym (snd f)) (cong (fst f) (σ B b)) (snd f) (~ i) j)
      snd (lemma i f) j = hcomp
        (λ k → λ { (i = i0) → doubleCompPath-filler refl
                      (cong (fst (sspm-counit X)) (push f (pt B) ∙ sym (push c (pt B)))) refl k j
                 ; (i = i1) → hcomp
                   (λ i → λ { (k = i0) → cong (λ q → sym (snd f) ∙∙ cong (fst f) q ∙∙ snd f)
                                              (σ-pt B) (~ i) j
                            ; (k = i1) → snd f (i ∧ j)
                            ; (j = i0) → snd f (~ k)
                            ; (j = i1) → snd f (i ∨ (~ k))})
                   (doubleCompPath-filler (sym (snd f)) refl (snd f) (~ k) j)
                 ; (j = i0) → snd f ((~ i) ∨ (~ k))
                 ; (j = i1) → doubleCompPath-filler {x = pt X} refl refl refl (~ k) i})
        (fst (sspm-counit X) (doubleCompPath-filler refl (push f (pt B))
          (sym (push c (pt B))) (~ i) j))

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

    transpose≡ψ : transpose ≡ ψ
    fst (transpose≡ψ i (h , h∙)) (inl a) = pt X
    fst (transpose≡ψ i (h , h∙)) (inr b) = pt X
    fst (transpose≡ψ i (h , h∙)) (push a b j) = ψ-path h a b j
    snd (transpose≡ψ i (h , h∙)) j =
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

-- If B is at the lowest level, then F and G preserve levels
-- and so we can apply PtdAdjunction
module _ (B : Pointed ℓ-zero) where
  private
    F : {ℓ : Level} → Pointed ℓ → Pointed ℓ
    F A = ∙join A B

    F→ : {ℓ ℓ' : Level}{A : Pointed ℓ}{A' : Pointed ℓ'} → (A →∙ A') → (F A →∙ F A')
    F→ = join-mapₗ B

    F→∘∙ : {ℓ ℓ' ℓ'' : Level}{A : Pointed ℓ}{A' : Pointed ℓ'}{A'' : Pointed ℓ''}
           (f' : A' →∙ A'')(f : A →∙ A') → F→ (f' ∘∙ f) ≡ F→ f' ∘∙ F→ f
    fst (F→∘∙ f' f i) (inl a) = inl (fst f' (fst f a))
    fst (F→∘∙ f' f i) (inr b) = inr b
    fst (F→∘∙ f' f i) (push a b j) = push (fst f' (fst f a)) b j
    snd (F→∘∙ f' f i) = cong-∙ inl (cong (fst f') (snd f)) (snd f') i

    G : {ℓ : Level} → Pointed ℓ → Pointed ℓ
    G X = ∙Susp (typ B) →∙ X ∙

    G→ : {ℓ ℓ' : Level}{X : Pointed ℓ}{X' : Pointed ℓ'} → (X →∙ X') → (G X →∙ G X')
    G→ = spmap-mapₗ B

    G→∘∙ : {ℓ ℓ' ℓ'' : Level}{X : Pointed ℓ}{X' : Pointed ℓ'}{X'' : Pointed ℓ''}
           (g' : X' →∙ X'')(g : X →∙ X') → G→ (g' ∘∙ g) ≡ G→ g' ∘∙ G→ g
    G→∘∙ {X'' = X''} g' g = →∙Homogeneous≡ (spmap-homogeneous B X'') lemma
      where
        lemma : fst (G→ (g' ∘∙ g)) ≡ fst (G→ g' ∘∙ G→ g)
        lemma i f = ∘∙-assoc g' g f i

  sspm-iso : (A : Pointed ℓA)(X : Pointed ℓX)
    → Iso (∙join A B →∙ X) (A →∙ (∙Susp (typ B) →∙ X ∙))
  sspm-iso = PtdAdjunctionIso F F F→ F→ F→∘∙ G G G→ G→ G→∘∙ F⊣G
    where
      F⊣G : PtdAdjunction F F F→ F→ G G G→ G→
      PtdAdjunction.ηˡ F⊣G = sspm-unit B
      PtdAdjunction.ηʳ F⊣G = sspm-unit B
      PtdAdjunction.η→ F⊣G = sspm-unit-nat B
      PtdAdjunction.εˡ F⊣G = sspm-counit B
      PtdAdjunction.εʳ F⊣G = sspm-counit B
      PtdAdjunction.ε→ F⊣G = sspm-counit-nat B
      PtdAdjunction.εF-Fη F⊣G = sspm-unit-counit B
      PtdAdjunction.Gε-ηG F⊣G = sspm-counit-unit B
