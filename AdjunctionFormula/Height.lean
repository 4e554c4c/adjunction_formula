-- import Mathlib.RingTheory.Ideal.basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.Order.KrullDimension
import Mathlib.Data.Real.ENNReal

import AdjunctionFormula.Notation

variable {R : Type _} [CommRing R]

namespace Ideal

variable (I : Ideal R)

@[reducible]
protected noncomputable def height  [h : IsPrime I] : WithBot ℕ∞ :=
  ⟨I, h⟩ |> height (PrimeSpectrum R)

theorem minimalPrimes_isPrime {I p : Ideal R} (h : p ∈ I.minimalPrimes) : p.IsPrime := sorry

end Ideal

noncomputable def Ring.dim (R : Type _) [CommRing R] : WithBot ℕ∞ :=
  krullDim (PrimeSpectrum R)

namespace Dimension

open Ring
open Ideal

lemma dim_eq_sup_heights_maximal :
    (dim R) = (⨆ (m : (MaximalSpectrum R)), (m.asIdeal.height)) := by
  sorry

corollary dim_eq_height_of_maximal_of_LocalRing [LocalRing R] :
    (dim R) = (LocalRing.maximalIdeal R).height := by
  sorry

-- the dimension of the local ring at p is the same as the height of p
corollary dim_localized_at_p_eq_height_p (p : Ideal R) [IsPrime p] :
    (dim (Localization.AtPrime p)) = p.height := sorry

theorem dim_minus_1_of_quotient_element_non_minimal (x : R) (hx : ∀ p ∈ minimalPrimes R, x ∉ p) :
    (dim (R ⧸ (Ideal.span {x}))) + 1 ≤ (dim R) := sorry

variable [IsNoetherianRing R]

-- Krull's Principal Ideal Theorem, aka the Hauptidealsatz
theorem minimal_primes_height_1_of_principal (x : R) :
    ∀ (h : p ∈ (Ideal.span {x}).minimalPrimes),
        haveI : IsPrime p := minimalPrimes_isPrime h
        p.height = 1 := by
  intros h
  haveI : IsPrime p := minimalPrimes_isPrime h
  rw [← dim_localized_at_p_eq_height_p p]
  set Aₚ := Localization.AtPrime p
  sorry

-- Krull's Height theroem
theorem minimal_primes_height_le_n_of_n_generators (xs : Finset R) :
    ∀ (h : p ∈ (Ideal.span xs.toSet).minimalPrimes),
        haveI : IsPrime p := minimalPrimes_isPrime h
        p.height ≤ xs.card := sorry

end Dimension
