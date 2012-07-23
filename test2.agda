module test2 where

open import Data.Nat
open import Data.List hiding (any)
open import Data.List.Any
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

open Membership (setoid ℕ)

data IsEmpty : List ℕ → Set where
  emp : IsEmpty []

open import Relation.Nullary

open import Relation.Binary
open DecTotalOrder decTotalOrder using (total) renaming (trans to ≤-trans; refl to ≤-refl)

max : (l : List ℕ) → ∃ (λ n → n ∈ l × (∀ m → m ∈ l → m ≤ n)) ⊎ IsEmpty l
max [] = inj₂ emp
max (x ∷ l) with max l
max (x ∷ l) | inj₁ (m , ml , mm) with total x m
... | inj₁ leq = inj₁ (m , (there ml) , (λ { .x (here refl) → leq ; m₁ (there x₂) → mm m₁ x₂ }))
... | inj₂ leq = inj₁ (x , (here refl) , (λ { .x (here refl) → ≤-refl ; m₁ (there x₁) → ≤-trans (mm m₁ x₁) leq }))
max (x ∷ .[]) | inj₂ emp = inj₁ (x , (here refl) , (λ { ._ (here refl) → ≤-refl ; m (there ()) }))

data _≤head_ : ℕ → List ℕ → Set where
  [] : ∀ n → n ≤head []
  _∷_ : ∀ {m n} → m ≤ n → ∀ l → m ≤head (n ∷ l)
  

data IsSorted : List ℕ → Set where
  [] : IsSorted []
  _∷_ : ∀ {l x} → x ≤head l → IsSorted l → IsSorted (x ∷ l)

data IsPermutation : List ℕ → List ℕ → Set where
  reflP : ∀ x → IsPermutation x x
  swapP : ∀ m n l → IsPermutation (m ∷ n ∷ l) (n ∷ m ∷ l)
  tailP : ∀ h l l' → IsPermutation l l' → IsPermutation (h ∷ l) (h ∷ l')
  transP : ∀ a b c → IsPermutation a b → IsPermutation b c → IsPermutation a c

-- _≟_ : (a b : ℕ) → Dec (a ≡ b)
-- a ≟ b = ?

cut : (l : List ℕ) -> {x : ℕ} -> x ∈ l -> List ℕ
cut .(x₁ ∷ xs) (here {x₁} {xs} px) = xs
cut .(x₁ ∷ xs) (there {x₁} {xs} xinl) = x₁ ∷ (cut xs xinl) 


IsPermutation' : List ℕ → List ℕ → Set
IsPermutation' [] b = IsEmpty b
IsPermutation' (x ∷ a) b = Σ (x ∈ b) (λ xinb ->  IsPermutation' a (cut b xinb))  

isEmpty? : ∀ l → Dec (IsEmpty l)
isEmpty? [] = yes emp
isEmpty? (_ ∷ _) = no (λ ())

isPermutation'? : ∀ a b → Dec (IsPermutation' a b)
isPermutation'? [] b = isEmpty? b
isPermutation'? (x ∷ a) b with any (_≟_ x) b
isPermutation'? (x ∷ a) b | no ¬p = no (λ x₁ → ¬p (proj₁ x₁))
isPermutation'? (x ∷ a) b | yes p with isPermutation'? a (cut b p)
isPermutation'? (x ∷ a) b | yes p | yes p₁ = yes (p , p₁)
isPermutation'? (x ∷ a) b | yes p | no ¬p = no (λ x₁ → {!!})
{-  go : Dec
      (Σ (Any (_≡_ x) b) (λ xinb → IsPermutation' a (cut b xinb))) -}

IsPermutation3 : List ℕ → List ℕ → Set
IsPermutation3 a b = ∀ x → Σ (x ∈ a → x ∈ b) (λ f →
                            Σ (x ∈ b → x ∈ a) (λ g → 
                            (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)))

open import Function

ip3-trans : ∀ a b c → IsPermutation3 a b → IsPermutation3 b c → IsPermutation3 a c
ip3-trans a b c abp bcp x with abp x | bcp x
... | (f₁ , g₁ , fg-inv₁ , gf-inv₁) | (f₂ , g₂ , fg-inv₂ , gf-inv₂) 
   = f₂ ∘ f₁ , (g₁ ∘ g₂) , ((λ x₁ → trans (cong f₂ (fg-inv₁ (g₂ x₁))) (fg-inv₂ x₁)) , (λ x₁ → trans (cong g₁ (gf-inv₂ (f₁ x₁))) (gf-inv₁ x₁)))

ip3-refl : ∀ a → IsPermutation3 a a
ip3-refl a x = id , id , (λ x₁ → refl) , (λ x₁ → refl)

ip3-sym : ∀ a b → IsPermutation3 a b → IsPermutation3 b a
ip3-sym a b perm x with perm x
... | f , g , fgi , gfi = g , f , gfi , fgi

ip3-swap : ∀ a b l → IsPermutation3 (a ∷ b ∷ l) (b ∷ a ∷ l)
ip3-swap a b l x = (λ { (here px) → there (here px) ; (there (here px)) → here px ; (there (there y)) → there (there y) }), ((λ { (here px) → there (here px) ; (there (here px)) → here px ; (there (there y)) → there (there y) })) , ((λ { (here px) → refl ; (there (here px)) → refl ; (there (there y)) → refl })) , (((λ { (here px) → refl ; (there (here px)) → refl ; (there (there y)) → refl })))


ip3-tail : ∀ h l l' -> IsPermutation3 l l' -> IsPermutation3 (h ∷ l) (h ∷ l')
ip3-tail h l l' ip3ll x with ip3ll x 
... | (f , g , fg , gf) = (λ { (here px) → here px ; (there x) → there (f x) }) , ((λ { (here px) → here px ; (there x) → there (g x) })) , ((λ { (here px) → refl ; (there x) → cong there (fg x)})) , (((λ { (here px) → refl ; (there x) → cong there (gf x)})))

ip3 : ∀ a b -> IsPermutation a b -> IsPermutation3 a b
ip3 .b b (reflP .b) = ip3-refl b
ip3 .(m ∷ n ∷ l) .(n ∷ m ∷ l) (swapP m n l) = ip3-swap m n l
ip3 .(h ∷ l) .(h ∷ l') (tailP h l l' ipab) = ip3-tail h l l' (ip3 l l' ipab)
ip3 .a .c (transP a b c ipab ipbc) = ip3-trans a b c (ip3 a b ipab) (ip3 b c ipbc)

ipun3 : ∀ a b -> IsPermutation3 a b -> IsPermutation a b
ipun3 [] [] perm = reflP []
ipun3 [] (x ∷ b) perm with perm x
... | f , g , fg , gf with g (here refl)
ipun3 [] (x ∷ b) perm | f , g , fg , gf | ()
ipun3 (x ∷ a) b perm with perm x
... | f , g , fg , gf = transP (x ∷ a) (x ∷ b') b (tailP x a b' {!!}) {!!} where
  fh = f (here refl)
  b' = cut b fh

good : ∀ {a b} → (IsPermutation a b → IsPermutation' a b) × (IsPermutation' a b → IsPermutation a b)
good = {!!}


Sort = (l : List ℕ) → ∃ (λ l' → IsSorted l' × IsPermutation l l')
