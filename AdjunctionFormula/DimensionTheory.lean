import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Noetherian
import AdjunctionFormula.PrimaryDecomposition
import AdjunctionFormula.Height

namespace Dimension

open Ring
open Ideal

variable (R : Type _) [CommRing R] [LocalRing R]

noncomputable def minimal_size_of_genset_of_primary_ideal :
(WithBot (WithTop ℕ)) :=
-- ⨅ (s : Finset R), s.card
⨅ (s ∈
{s : Finset R | IsPrimaryWithRadical (Ideal.span s.toSet) (LocalRing.maximalIdeal R)}), s.card

-- part of the dimension theorem, technically
theorem dim_eq_height_maximal :
dim R = height (LocalRing.maximalIdeal R) := sorry

end Dimension

namespace Dimension

open Ideal

variable (R : Type _) [CommRing R] [IsNoetherian R R]

lemma exist_subideals_of_all_heights_of_height_n
(I : Ideal R) (n : ℕ) (hI : n = height I) :
∃ f : Fin n → R, ∀ i : ℕ, i < n →
(height (Ideal.span (f  '' {a | a ≤ i}))) = i := sorry

end Dimension

namespace DimensionTheory

open Ring
open Dimension

variable (R : Type _) [CommRing R] [LocalRing R] [IsNoetherian R R]

-- the dimension theorem, see Bruns-Herzog appendix A
theorem dim_eq_minimal_size_of_genset_of_primary_ideal :
dim R = minimal_size_of_genset_of_primary_ideal R := sorry


end DimensionTheory


