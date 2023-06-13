
\begin{code}

{-# OPTIONS --prop --rewriting #-}

open Agda.Primitive
open import Equality
open import Logic
open import Nat

module Integers where

-- The initial model for integers

module I where
  postulate
    Z       : Set
    Zero    : Z
    Suc     : Z → Z
    Pred    : Z → Z
    SucPred : ∀{i} → Suc (Pred i) ≡ i
    PredSuc : ∀{i} → Pred (Suc i) ≡ i

-- then the general definition of a model M
-- with the recursor, homomorphisme from I to M, we can postulate the comutation properties

record Model {l} : Set (lsuc l) where
  field
    Z       : Set l
    Zero    : Z
    Suc     : Z → Z
    Pred    : Z → Z
    SucPred : ∀{i} → Suc (Pred i) ≡ i
    PredSuc : ∀{i} → Pred (Suc i) ≡ i
  postulate
    ⟦_⟧     : I.Z → Z
    ⟦Zero⟧  : ⟦ I.Zero ⟧ ≡ Zero
    ⟦Suc⟧   : ∀{i} → ⟦ I.Suc i ⟧ ≡ Suc ⟦ i ⟧
    ⟦Pred⟧  : ∀{i} → ⟦ I.Pred i ⟧ ≡ Pred ⟦ i ⟧
    {-# REWRITE ⟦Zero⟧ ⟦Suc⟧ ⟦Pred⟧ #-}

-- Using the recursor we can define the addition :
-- we want a function _+_ : I.Z → I.Z → I.Z
-- we can define it as a recursor to a model

addTo : I.Z -> Model
addTo a = record
  { Z       = I.Z
  ; Zero    = a
  ; Suc     = I.Suc
  ; Pred    = I.Pred
  ; SucPred = I.SucPred
  ; PredSuc = I.PredSuc
  }
module addTo a = Model (addTo a)

_+_ : I.Z → I.Z → I.Z
i + j = addTo.⟦_⟧ j i
infix 5 _+_

-- then we need induction and dependent model to prove things on addition

record DepModel {l} : Set (lsuc l) where
  field
    Z•       : I.Z -> Set l
    Zero•    : Z• I.Zero
    Suc•     : ∀{i} → Z• i → Z• (I.Suc i)
    Pred•    : ∀{i} → Z• i → Z• (I.Pred i)
    SucPred• : ∀{i} → (i• : Z• i) → transp⟨ Z• ⟩ I.SucPred (Suc• (Pred• i•)) ≡ i•
    PredSuc• : ∀{i} → (i• : Z• i) → (transp⟨ Z• ⟩ I.PredSuc (Pred• (Suc• i•))) ≡ i•
  postulate
    ind : (i : I.Z) → Z• i
    indZero : ind(I.Zero) ≡ Zero•
    indSuc : ∀{i} → ind(I.Suc i) ≡ Suc• (ind i)
    indPred : ∀{i} → ind(I.Pred i) ≡ Pred• (ind i)
    {-# REWRITE indZero indSuc indPred #-}

\end{code}

Using induction we can prove some properites like :
  - existence of a neutral element for addition
  - associativity of addition
  - comutativity of addition
  - existence of an inverse
  - ...

\begin{code}

-- Addition Associativity

+assocProof : I.Z → I.Z → DepModel
+assocProof b c = record
  { Z•       = λ a → Lift ((a + b) + c ≡ a + (b + c))
  ; Zero•    = ⟪ refl ⟫
  ; Suc•     = λ HR → ⟪ cong⟨ I.Suc ⟩ (unfold HR) ⟫
  ; Pred•    = λ HR → ⟪ cong⟨ I.Pred ⟩ (unfold HR) ⟫
  ; SucPred• = λ _ → refl 
  ; PredSuc• = λ _ → refl
  }

+assoc : (a b c : I.Z) → (a + b) + c ≡ a + (b + c)
+assoc a b c = unfold (DepModel.ind (+assocProof b c) a)

-- Neutral Element for Addition

+NeutralRightProof : DepModel
+NeutralRightProof = record
  { Z•       = λ i → Lift ((i + I.Zero) ≡ i)
  ; Zero•    = ⟪ refl ⟫
  ; Suc•     = λ HR → ⟪ cong⟨ I.Suc ⟩ (unfold HR) ⟫
  ; Pred•    = λ HR → ⟪ cong⟨ I.Pred ⟩ (unfold HR) ⟫
  ; SucPred• = λ i• → refl
  ; PredSuc• = λ i• → refl
  }

+Neutral : (i : I.Z) → ((i + I.Zero) ≡ i) ∧ ((I.Zero + i) ≡ i)
+Neutral i = (unfold (DepModel.ind +NeutralRightProof i)),
             refl


+commLemmaSucProof : I.Z → DepModel
+commLemmaSucProof b = record
 { Z• = λ a → Lift ((I.Suc a) + b ≡ a + (I.Suc b))
 ; Zero• = ⟪ refl ⟫
 ; Suc•     = λ {⟪ HR ⟫ → ⟪ cong⟨ I.Suc ⟩ HR ⟫}
 ; Pred•    = λ {a} HR → ⟪ ((I.Suc (I.Pred a)) + b) ≡⟨ I.SucPred ⟩
                          (a + b)                 ≡⟨ symetry I.PredSuc ⟩
                          (cong⟨ I.Pred ⟩ (unfold HR)) ⟫
 ; SucPred• = λ _ → refl
 ; PredSuc• = λ _ → refl
 }

+commLemmaSuc : (a b : I.Z) → (I.Suc a) + b ≡ a + (I.Suc b)
+commLemmaSuc a b = unfold (DepModel.ind (+commLemmaSucProof b) a)

+commLemmaPredProof : I.Z → DepModel
+commLemmaPredProof b = record
 { Z• = λ a → Lift ((I.Pred a) + b ≡ a + (I.Pred b))
 ; Zero• = ⟪ refl ⟫
 ; Suc•  = λ {a} HR → ⟪ ((I.Pred (I.Suc a)) + b) ≡⟨ I.PredSuc ⟩
                           (a + b)                 ≡⟨ symetry I.SucPred ⟩
                           (cong⟨ I.Suc ⟩ (unfold HR)) ⟫
 ; Pred• = λ HR → ⟪ cong⟨ I.Pred ⟩ (unfold HR) ⟫
 ; SucPred• = λ _ → refl
 ; PredSuc• = λ _ → refl
 }

+commLemmaPred : (a b : I.Z) → (I.Pred a) + b ≡ a + (I.Pred b)
+commLemmaPred a b = unfold (DepModel.ind (+commLemmaPredProof b) a)

+commProof : I.Z → DepModel
+commProof b = record
  { Z• = λ a → Lift (a + b ≡ b + a)
  ; Zero• = ⟪ symetry (unfold (DepModel.ind +NeutralRightProof b)) ⟫
  ; Suc• = λ {a} HR → ⟪ ((I.Suc a) + b) ≡⟨ cong⟨ I.Suc ⟩ (unfold HR) ⟩ (+commLemmaSuc b a) ⟫
  ; Pred• = λ {a} HR → ⟪ ((I.Pred a) + b) ≡⟨ cong⟨ I.Pred ⟩ (unfold HR) ⟩ (+commLemmaPred b a) ⟫
  ; SucPred• = λ _ → refl
  ; PredSuc• = λ _ → refl
  }

+comm : (a b : I.Z) → a + b ≡ b + a
+comm a b = unfold (DepModel.ind (+commProof b) a)

-- Inverse for Addition

negation : Model
negation = record
  { Z = I.Z
  ; Zero = I.Zero
  ; Suc = λ i → I.Pred i
  ; Pred = λ i → I.Suc i
  ; SucPred = I.PredSuc
  ; PredSuc = I.SucPred
  }
module negation = Model negation

-_ : I.Z → I.Z
-_ = negation.⟦_⟧

+InverseProof : DepModel
+InverseProof = record
  { Z• = λ i → Lift (- i + i ≡ I.Zero)
  ; Zero• = ⟪ refl ⟫
  ; Suc• = λ {i} HR → ⟪ - (I.Suc i) + (I.Suc i) ≡⟨ cong⟨ I.Pred ⟩ (symetry (+commLemmaSuc (- i) i)) ⟩
                        I.Pred (I.Suc (- i + i)) ≡⟨ I.PredSuc ⟩ (unfold HR) ⟫
  ; Pred• = λ {i} HR → ⟪ - (I.Pred i) + (I.Pred i) ≡⟨ cong⟨ I.Suc ⟩ (symetry (+commLemmaPred (- i) i)) ⟩
                        I.Suc (I.Pred (- i + i)) ≡⟨ I.SucPred ⟩ (unfold HR) ⟫
  ; SucPred• = λ _ → refl
  ; PredSuc• = λ _ → refl
  }

+Inverse : (i : I.Z) → (- i + i ≡ I.Zero)
+Inverse i = unfold (DepModel.ind +InverseProof i)

\end{code}

We want now to proof normalisation of QIIT integers :
  - describe the normal form
    (model without equalities)
  - prove the inclusion
    (every normal form is actually an integer)
  - prove the normalisation
    (every integers has a normal form
  - thoses two steps are homomorphism
  - thoses are both stable

\begin{code}

-- Normal Forms

data NFZ : Set where
  -Nat : ℕ → NFZ
  Zero : NFZ
  +Nat : ℕ → NFZ

-- Inclusion

⌜_⌝ : NFZ → I.Z
⌜ -Nat zero ⌝     = I.Pred I.Zero
⌜ -Nat (succ i) ⌝ = I.Pred ⌜ -Nat i ⌝
⌜ Zero ⌝          = I.Zero
⌜ +Nat zero ⌝     = I.Suc I.Zero
⌜ +Nat (succ i) ⌝ = I.Suc ⌜ +Nat i ⌝

-- Normalisation

NormModel : Model
NormModel = record
  { Z = NFZ
  ; Zero    = Zero
  ; Suc     = λ { ( -Nat zero     ) → Zero
                ; ( -Nat (succ i) ) → -Nat i
                ; ( Zero          ) → +Nat zero
                ; ( +Nat i        ) → +Nat (succ i)
                }
  ; Pred    = λ { ( -Nat i        ) → -Nat (succ i)
                ; ( Zero          ) → -Nat zero
                ; ( +Nat zero     ) → Zero
                ; ( +Nat (succ i) ) → +Nat i
                }
  ; SucPred = λ { { -Nat zero     } → refl
                ; { -Nat (succ i) } → refl
                ; { Zero          } → refl
                ; { +Nat zero     } → refl
                ; { +Nat (succ i) } → refl
                }
  ; PredSuc = λ { { -Nat zero     } → refl
                ; { -Nat (succ i) } → refl
                ; { Zero          } → refl
                ; { +Nat zero     } → refl
                ; { +Nat (succ i) } → refl
                }
  }

module NormModel = Model NormModel

norm : I.Z → NFZ
norm = NormModel.⟦_⟧

-- Homomorphism

normZeroMorph : ⌜ NormModel.Zero ⌝ ≡ I.Zero
normZeroMorph = refl

normSucMorph : (nf : NFZ) → ⌜ NormModel.Suc nf ⌝ ≡ I.Suc ⌜ nf ⌝
normSucMorph = λ { ( -Nat zero     ) → symetry I.SucPred
                 ; ( -Nat (succ i) ) → symetry I.SucPred
                 ; ( Zero          ) → refl
                 ; ( +Nat x        ) → refl
                 }

normPredMorph : (nf : NFZ) → ⌜ NormModel.Pred nf ⌝ ≡ I.Pred ⌜ nf ⌝
normPredMorph = λ { ( -Nat x        ) → refl
                  ; ( Zero          ) → refl
                  ; ( +Nat zero     ) → symetry I.PredSuc
                  ; ( +Nat (succ i) ) → symetry I.PredSuc
                  }

-- norm is stable by definition (recursor for a I.Z model)

-- Stability

NormStability : (nf : NFZ) → norm ⌜ nf ⌝ ≡ nf
NormStability (-Nat zero) =
  refl
NormStability (-Nat (succ i)) =
  cong⟨ NormModel.Pred ⟩ (NormStability (-Nat i))
NormStability Zero =
  refl
NormStability (+Nat zero) =
  refl
NormStability (+Nat (succ i)) =
  cong⟨ NormModel.Suc ⟩ (NormStability (+Nat i))

InclusionStabilityProof : DepModel
InclusionStabilityProof = record
  { Z•       = λ i → Lift (⌜ norm i ⌝ ≡ i)
  ; Zero•    = ⟪ refl ⟫
  ; Suc•     = λ {i} i• → ⟪ ⌜ norm (I.Suc i) ⌝ ≡⟨ normSucMorph (norm i) ⟩ (cong⟨ I.Suc ⟩ (unfold i•)) ⟫
  ; Pred•    = λ {i} i• → ⟪ ⌜ norm (I.Pred i) ⌝ ≡⟨ normPredMorph (norm i) ⟩ (cong⟨ I.Pred ⟩ (unfold i•)) ⟫
  ; SucPred• = λ _ → refl
  ; PredSuc• = λ _ → refl
  }

InclusionStability : (i : I.Z) → ⌜ norm i ⌝ ≡ i
InclusionStability i = unfold (DepModel.ind InclusionStabilityProof i)

\end{code}
