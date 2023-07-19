import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations

open Ideal

variable {R : Type _} [CommRing R]

def IsPrimaryWithRadical (I p : Ideal R) : Prop :=
IsPrimary I ∧ radical I = p

