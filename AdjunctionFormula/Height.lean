-- import Mathlib.RingTheory.Ideal.basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.Order.KrullDimension

import AdjunctionFormula.Notation

variable {R : Type _} [CommRing R]

section Ideal

variable (I : Ideal R)

instance (p : I.minimalPrimes) : Ideal.IsPrime (p : Ideal R) := by
  sorry

end Ideal

noncomputable section

@[reducible]
protected noncomputable def Ideal.height (I : Ideal R) [h : IsPrime I] : WithBot ℕ∞ :=
  PrimeSpectrum.mk I h |> height (PrimeSpectrum R)

noncomputable def Ring.dim (R : Type _) [CommRing R] : WithBot ℕ∞ :=
  krullDim (PrimeSpectrum R)

namespace Dimension

open Ring
open Ideal

lemma dim_eq_sup_heights_maximal :
    (dim R) = (⨆ (m : (MaximalSpectrum R)), (m.asIdeal.height)) :=
  sorry

corollary dim_eq_height_of_maximal_of_LocalRing [LocalRing R] :
    (dim R) = (LocalRing.maximalIdeal R).height := sorry

-- the dimension of the local ring at p is the same as the height of p
corollary dim_localized_at_p_eq_height_p (p : Ideal R) [IsPrime p] :
    (dim (Localization.AtPrime p)) = p.height := sorry
-- note bug in docs of line 67-68 of Mathlib/RingTheory/AtPrime.lean???, I vs P, R vs S

theorem dim_minus_1_of_quotient_element_non_minimal (x : R)
  (hx : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
    (dim (R ⧸ (Ideal.span {x}))) + 1 ≤ (dim R) := sorry

-- Krull's Principal Ideal Theorem, aka the Hauptidealsatz
theorem minimal_primes_height_1_of_principal (x : R) :
    ∀ p ∈ (Ideal.span {x}).minimalPrimes, p.height = 1 := sorry

-- Krull's Height theroem
theorem minimal_primes_height_n_of_n_generators (xs : Finset R) :
    ∀ p ∈ (Ideal.span xs.toSet).minimalPrimes, p.height = xs.card := sorry

end Dimension
