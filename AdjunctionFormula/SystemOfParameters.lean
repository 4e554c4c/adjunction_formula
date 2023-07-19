import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.LocalRing
import AdjunctionFormula.PrimaryDecomposition


-- There's two ways one could decide to define a system of paramaters.
--
-- 1. A systen of parameters is a generating set for an m-primary ideal
--    whose length is minimal among all such lengths. Informally, it is a generating
--    set that realizes nu in the dimension theorem. This is in some sense
--    what it "really is", and then is a theorem that the length of every system
--    of parameters is the dimension.
-- 2. A system of parameters is a generating set for an m-primary ideal
--    whose length is the dimension of the (local) ring. This seems
--    way easier to work with, both for humans and in lean, but has the
--    disadvantage of needing to wait for the dimension theorem to show that
--    such a system of parameters is minimal.
--
-- I'm pretty sure that option (2) is the correct way to go.

variable {R : Type _} [CommRing R] [LocalRing R]

def IsSystemOfParameters (s : Finset R) : Prop :=
IsPrimaryWithRadical (LocalRing.maximalIdeal R) (Ideal.span s)
