\begin{code}

-- Definition for propositional equality with some properties

{-# OPTIONS --rewriting #-}

open import Logic

module Equality where

  infix 4 _≡_
  infixr 2 _≡⟨_⟩_

  id : ∀{l}{A : Set l} → A → A
  id = λ x → x

  -- Equality

  data _≡_ {l}{A : Set l}(x : A) : A → Set l where
    refl : x ≡ x

  {-# BUILTIN REWRITE _≡_ #-}

  -- Properities

  symetry : ∀{l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
  symetry refl = refl

  transitivity : ∀{l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  transitivity refl refl = refl

  uniqueness : ∀{l}{A : Set l}{x y : A} → (p : x ≡ y) → (p' : x ≡ y) → p ≡ p'
  uniqueness refl refl = refl

  _≡⟨_⟩_ : ∀{l}{A : Set l}{y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ eqy ⟩ eqz = transitivity eqy eqz

  -- (lemma 2.2.1 HoTT)
  cong⟨_⟩ : ∀{l}{A : Set l}{l'}{B : Set l'}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
  cong⟨ f ⟩ refl = refl
  
  -- (lemma 2.3.2 HoTT)
  transp⟨_⟩ : ∀{l}{A : Set l}{l'}(P : A → Set l'){x y : A} → x ≡ y → P x → P y
  transp⟨ P ⟩ refl = id

  -- (lemma 2.3.4 HoTT)
  congd⟨_⟩ : ∀{l}{A : Set l}{l'}(P : A → Set l')(f : (a : A) → P a){x y : A} → (eq : x ≡ y) → (transp⟨ P ⟩ eq) (f x) ≡ f y 
  congd⟨ P ⟩ f refl = refl

  -- (theorem 2.7.2 HoTT)
  transpGen : ∀{l}{A : Set l}{l'}{P : A → Set l'} → (w w' : ∃ (λ (x : A) → P x)) →
                                               ((w ≡ w') → ∃ (λ (p : pr₁ w ≡ pr₁ w') → transp⟨ P ⟩ p (pr₂ w) ≡ (pr₂ w')))
  transpGen _ _ refl = ⟨ refl , refl ⟩

  postulate transpEq : ∀{l}{A : Set l}{l'}{B : Set l'}{f g : A → B}{x y : A} →
                       (px : f(x) ≡ g(x)) → (py : f(y) ≡ g(y)) → (eq : x ≡ y) → (transp⟨ (λ a → f(a) ≡ g(a)) ⟩ eq) px ≡ py
  -- transpEq refl refl refl = refl                                              (should working ?)
  -- transpEq {x = x}{y = y} _ _ refl = pr₂ (transpGen ⟨ x , _ ⟩ ⟨ y , _ ⟩ refl) (also not working ?)

  -- Functional extensionality (Axiom 2.9.3 HoTT)

  postulate funext  : ∀{l}{A : Set l}{l'}{B : Set l'}{f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
  funexti : ∀{l}{A : Set l}{l'}{B : Set l'}{f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g
  funexti p = funext (λ a → p {x = a})


\end{code}
