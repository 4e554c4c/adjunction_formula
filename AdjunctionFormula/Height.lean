-- import Mathlib.RingTheory.Ideal.basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime

namespace Ideal

variable {R : Type _} [CommRing R]

---def Height {p : Ideal R} (hp : p.IsPrime) : Int := sorry
-- sup of lengths of chains of prime ideals

--this is actually in mathlib for preorders or something, but remember to take the
--set of PRIME ideals, not the set of ideals

noncomputable def height (I : Ideal R) : WithBot (WithTop ℕ) := ⨆ (p : I.minimalPrimes), sorry--p.height
-- sup of heights of primes containing this ideal

lemma height_eq_prime_height (I : Ideal R) [IsPrime I] :
height I = I.height := sorry

--this is not already in mathlib


end Ideal

namespace Ring

noncomputable def dim (R : Type _) [CommRing R] : WithBot (WithTop ℕ) := ⨆ (m : MaximalSpectrum R), (height m)
-- sup of heights of all primes in R (i.e. the krull dim of the maximal spectrum)
-- also in mathlib for preorders, I think

end Ring

namespace Dimension

open Ring
open Ideal

variable {R : Type _} [CommRing R]

lemma dim_eq_sup_heights_maximal :
(dim R) = (⨆ (m : (MaximalSpectrum R)), (height m.asIdeal)) :=
sorry

-- this is a corollary, not a theorem... where did the keyword go??
theorem dim_eq_height_of_maximal_of_LocalRing [LocalRing R] :
(dim R) = (height (LocalRing.maximalIdeal R)) := sorry

-- this is a corollary, not a theorem... where did the keyword go??
-- the dimension of the local ring at p is the same as the height of p
theorem dim_localized_at_p_eq_height_p (p : Ideal R) [IsPrime p] :
(dim (Localization.AtPrime p)) = (height p) := sorry
-- note bug in docs of line 67-68 of Mathlib/RingTheory/AtPrime.lean???, I vs P, R vs S

variable (y : WithTop (WithBot ℕ))

#check (↑y) - (1 : WithTop (WithBot ℤ))


-- theorem dim_minus_1_of_quotient_element_non_principal (x : R)
-- (hx : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
-- (dim (R ⧸ {x})) ≤ (↑(dim R) : WithBot (WithTop ℤ)) - (1 : WithBot (WithTop ℤ)) := sorry

-- the theorem about quotienting by an element in a non-minimal prime decreases height by
--   (at least) one

-- Krull's height theorem can go here (along with the prinicipal ideal theorem)

end Dimension
--↥↑', '↥', '⇑