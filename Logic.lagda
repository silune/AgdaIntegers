\begin{code}

open import Agda.Primitive

module Logic where

  infixr 4 ⟨_,_⟩
  infixr 5 _∨_
  infixr 6 _∧_

  -- Unit type
  data ⊤ : Set where
    triv : ⊤

  -- Empty type
  data ⊥ : Set where

  -- Negation
  ¬ : Set → Set
  ¬ A = A → ⊥

  -- Conjunction
  data _∧_ (A B : Set) : Set where
    _,_ : A → B → A ∧ B

  -- Disjunction
  data _∨_ (A B : Set) : Set where
    left  : A → A ∨ B
    right : B → A ∨ B

  -- Existential Quantifier
  data ∃ {l}{A : Set l}{l'} (B : A → Set l') : Set (l ⊔ l')  where
    ⟨_,_⟩ : (x : A) → B x → ∃ B

  pr₁ : ∀{l}{A : Set l}{l'}{B : A → Set l'} → (∃ B) → A
  pr₁ ⟨ e , _ ⟩ = e

  pr₂ : ∀{l}{A : Set l}{l'}{B : A → Set l'} → (p : ∃ B) → B (pr₁ p)
  pr₂ ⟨ _ , p ⟩ = p

 \end{code}
