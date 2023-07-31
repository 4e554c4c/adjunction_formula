import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

variable {R : Type _} [CommRing R]
variable (M : Type _) [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

-- The prime avoidance lemma
-- theorem prime_avoidance (n m : ℕ)
-- (ps : Fin n → PrimeSpectrum R) (xs : Fin m → M) :
-- Submodule.span {(xs i) | i : Fin m} = ⊤ := sorry
-- this is not true, finish later

theorem prime_avoidance_1 (n : ℕ) (I : Ideal R)
(ps : Fin n → PrimeSpectrum R) (hI : ∀ j, ¬ (I ≤ (ps j).asIdeal)) :
(∃ x : R, ∀ j, ¬ (x ∈ (ps j).asIdeal)) := sorry