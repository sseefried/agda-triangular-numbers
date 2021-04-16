{-# OPTIONS --without-K #-}

module Triangular where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; module ≡-Reasoning)

-- Definition of a function to calculate Triangular Numbers
triangular : ℕ → ℕ
triangular zero = zero
triangular (suc n) = suc n + triangular n

n+1≡suc_n : ∀ {n : ℕ} → n + 1 ≡ suc n 
n+1≡suc_n {zero} = refl
n+1≡suc_n {suc n} = begin
  suc n + 1            ≡⟨⟩
  suc (n + 1)          ≡⟨ cong suc n+1≡suc_n ⟩
  suc (suc n)          ∎
  where
    open ≡-Reasoning

n+2≡suc_n+1 : ∀ {n : ℕ} → n + 2 ≡ suc n + 1
n+2≡suc_n+1 {zero}  = refl
n+2≡suc_n+1 {suc n} = begin
  suc n + 2             ≡⟨⟩
  suc (n + 2)           ≡⟨ cong suc (n+2≡suc_n+1) ⟩
  suc (suc n) + 1       ∎
  where
    open ≡-Reasoning

m%n+1<n+1 : ∀ m n → m % suc n < suc n
m%n+1<n+1 = m%n<n

leqMod2 : ∀ m n {≢0} → (2 * m  % 2) {≢0} + (n % 2) {≢0} < 2
leqMod2 m n =  begin-strict
  (2 * m % 2) + (n % 2)               ≡⟨ cong (λ x → (x % 2) + (n % 2)) (*-comm 2 m )  ⟩
  (m * 2 % 2) + (n % 2)               ≡⟨ cong (λ x → x + n % 2) (m*n%n≡0 m 1) ⟩
  0 + n % 2                           ≡⟨⟩
  n % 2                               <⟨ m%n+1<n+1 n 1 ⟩
  2                                   ∎
  where
    open ≤-Reasoning

-- Proof that the closed form is true
closedForm : ∀ n → triangular n ≡ (n * (n + 1)) / 2
closedForm zero = refl
closedForm (suc m) = begin
  triangular (suc m)                     ≡⟨⟩
  suc m + triangular m                   ≡⟨ cong (_+_ (suc m)) (closedForm m) ⟩
  suc m + ((m * (m + 1)) / 2)            ≡⟨ cong (λ x → suc m + ((m * x)) / 2) n+1≡suc_n ⟩
  suc m + ((m * suc m) / 2)              ≡⟨ cong (λ x → x + ((m * (suc m)) / 2)) (sym (m*n/n≡m (suc m) 2)) ⟩
  (suc m * 2) / 2 + ((m * suc m) / 2)    ≡⟨ cong (λ x → x / 2 + ((m * suc m) / 2)) ((*-comm (suc m) 2)) ⟩ 
  (2 * suc m) / 2 + ((m * suc m) / 2)    ≡⟨ sym (+-distrib-/ (2 * suc m) (m * suc m) (leqMod2 (suc m) (m * suc m))) ⟩
  (2 * suc m + m * (suc m)) / 2          ≡⟨ cong (λ x → x / 2) (sym (*-distribʳ-+ (suc m) 2 m)) ⟩
  ((2 + m) * suc m) / 2                  ≡⟨ cong (λ x → x / 2) (*-comm (2 + m) (suc m)) ⟩
  (suc m * (2 + m)) / 2                  ≡⟨ cong (λ x → (suc m * x) / 2) (+-comm 2 m) ⟩
  (suc m * (m + 2)) / 2                  ≡⟨ cong (λ x → (suc m *  x) / 2) (n+2≡suc_n+1 {m}) ⟩
  (suc m * (suc m + 1)) / 2              ∎
  where
    open ≡-Reasoning

-- An attempt to see if the proof is easier when you don't use _/_
closedForm2 : ∀ n → 2 * triangular n ≡ n * (n + 1)
closedForm2 zero = refl
closedForm2 (suc m) = begin
  2 * triangular (suc m)                 ≡⟨⟩
  2 * (suc m + triangular m)             ≡⟨ *-distribˡ-+ 2 (suc m) _ ⟩
  2 * suc m + 2 * triangular m           ≡⟨ cong (λ x → 2 * suc m + x) (closedForm2 m)  ⟩
  2 * suc m + m * (m + 1)                ≡⟨ cong (λ x → 2 * suc m + m * x) n+1≡suc_n ⟩
  2 * suc m + m * suc m                  ≡⟨ sym (*-distribʳ-+ (suc m) 2 m)  ⟩
  (2 + m) * suc m                        ≡⟨ *-comm (2 + m) (suc m)  ⟩
  suc m * (2 + m)                        ≡⟨ cong (λ x → suc m * x) (+-comm 2 m) ⟩
  suc m * (m + 2)                        ≡⟨ cong (λ x → suc m * x) n+2≡suc_n+1 ⟩
  suc m * (suc m + 1)                    ∎
  where
    open ≡-Reasoning
