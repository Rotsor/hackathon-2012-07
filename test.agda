module test where

open import Data.Nat using (zero; suc; _+_; _*_ ; _<_; _≤_ ; z≤n; _≟_) renaming (ℕ to Nat)
import Algebra
import Data.Nat.Properties as Props

open import Data.Empty
open import Function
open import Relation.Nullary

module Cheat = Algebra.CommutativeSemiring Props.commutativeSemiring
open Cheat using (+-assoc; +-comm; +-identity)
open import Data.Product
*-identityˡ = proj₁ (Cheat.*-identity)

open import Relation.Binary.PropositionalEquality


distr : (a b c : Nat) -> a * c + b * c ≡ (a + b) * c
distr zero b c = refl
distr (suc a) b c = trans (+-assoc c (a * c) (b * c)) (cong (λ x -> c + x) (distr a b c))


mulassoc : (a b c : Nat) -> a * (b * c) ≡ (a * b) * c 
mulassoc zero b c = refl
mulassoc (suc a) b c = trans (cong (_+_ (b * c)) (mulassoc a b c)) (distr b (a * b) c)

mulrightzero : (a : Nat) -> 0 ≡ a * 0
mulrightzero zero = refl
mulrightzero (suc a) = mulrightzero a


mulright : (a b : Nat) -> b + b * a ≡ b * suc a
mulright a zero = refl
mulright a (suc b) = cong suc (trans (+-comm b (a + b * a)) (trans (+-assoc a (b * a) b) (cong (_+_ a) (trans (+-comm (b * a) b ) (mulright a b) ))))


obvious : (x d : Nat) -> x ≤ d -> x ≢ d -> x < d
obvious .0 zero z≤n xneqd = ⊥-elim (xneqd refl)
obvious .0 (suc d) z≤n xneqd = Data.Nat.s≤s z≤n
obvious .(suc m) .(suc n) (Data.Nat.s≤s {m} {n} xled) xneqd = Data.Nat.s≤s (obvious m n xled (xneqd ∘ (cong suc)))

mulcom : (a b : Nat) -> a * b ≡ b * a
mulcom zero b = mulrightzero b
mulcom (suc a) b = trans (cong (_+_ b) (mulcom a b)) (mulright a b)

obvious2 : (i d : Nat) -> i < d -> 0 < d
obvious2 i zero ()
obvious2 i (suc d) i<d = Data.Nat.s≤s z≤n

obvious3 : (i n : Nat) -> i + suc n ≡ suc i + n
obvious3 zero n = refl
obvious3 (suc i) n = cong suc (obvious3 i n)

divmod' : (n d i : Nat) -> (i < d) -> Σ Nat (λ q -> Σ Nat (λ r -> i + n ≡ q * d + r × r < d))
divmod' zero d i i<d = 0 , i , proj₂ +-identity i , i<d
divmod' (suc n) d i i<d with (suc i ‌‌≟ d)
divmod' (suc n) d i i<d | yes p with divmod' n d 0 (obvious2 i d i<d)
... | q , r , good , small = suc q , r , trans (obvious3 i n) (trans (cong (λ x -> x + n) p ) (trans (cong (_+_ d) good) (sym (+-assoc d (q * d) r)))) , small
divmod' (suc n) d i i<d | no ¬p with divmod' n d (suc i) (obvious (suc i) d i<d ¬p) 
... | q , r , good , small = q , r ,  trans (trans (+-comm i (suc n)) (cong suc (+-comm n i))) good , small



divmod : (n d : Nat) -> (0 < d) -> Σ Nat (λ q -> Σ Nat (λ r -> n ≡ q * d + r × r < d))
divmod n d nonzerod = divmod' n d 0 nonzerod


open import IO
open import Data.Nat.Show

main : _
main = run (putStrLn (show (proj₁ (divmod 100000 10 (Data.Nat.s≤s z≤n)))))
