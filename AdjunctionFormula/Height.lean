import Mathlib.RingTheory.Ideal.basic


namespace Height

variable {R : Type _} [CommRing R]

def Height {p : Ideal R} (hp : p.IsPrime) : Int := sorry
-- sup of lengths of chains of prime ideals

--this is actually in mathlib for preorders or something, but remember to take the
--set of PRIME ideals, not the set of ideals

def Height (I : Ideal R) : Int := sorry
-- sup of heights of primes containing this

--this is not already in mathlib

--lemma height_is_sup (I : Ideal R) :
--(Height I = Sup {lengths of chains of primes containing I}) := sorry

end Height

namespace Dim

variable (R : Type _) [CommRing R]

def Dim := sorry
-- sup of heights of all primes in R

-- also in mathlib for preorders

--lemma Dim_eq_sup_heights_maximal (Dim R) = ⨆ {m: maximal ideals}, m.Height

--corollary : if R is local, dimension is equal to the height of the maximal ideal
--corollary : dimension of R_p is the same as the height of p

end Dim