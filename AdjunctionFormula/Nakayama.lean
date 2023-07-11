import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Torsion

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

open Ideal

open scoped BigOperators

variable (M)

def Submodule.mkqₛₗ (I : Ideal R) : M →ₛₗ[Ideal.Quotient.mk I] M ⧸ I • (⊤ : Submodule R M) :=
  { Submodule.mkQ _ with }
#align submodule.mkqₛₗ Submodule.mkqₛₗ

def Submodule.idqₛₗ (I : Ideal R) :
    M ⧸ I • (⊤ : Submodule R M) →ₛₗ[Ideal.Quotient.mk I] M ⧸ I • (⊤ : Submodule R M) :=
  { (LinearMap.id : M ⧸ I • (⊤ : Submodule R M) →ₗ[R] _) with }
#align submodule.idqₛₗ Submodule.idqₛₗ

@[simps apply]
def foobar (I : Ideal R) :
    Submodule R (M ⧸ I • (⊤ : Submodule R M)) ≃o Submodule (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))
    where
  toFun N := N.map (Submodule.idqₛₗ M I)
  invFun N := ⟨N.toAddSubmonoid, fun c x hx => N.smul_mem (Submodule.Quotient.mk c) hx⟩
  left_inv N := by ext t; change _ ∈ id '' _ ↔ _; simp
  right_inv _ := by ext t; change _ ∈ id '' _ ↔ _; simp
  map_rel_iff' := by
    intro a b
    dsimp
    let a' : Set (M ⧸ I • (⊤ : Submodule R M)) := a
    let b' : Set (M ⧸ I • (⊤ : Submodule R M)) := b
    change id '' a' ≤ id '' b' ↔ a ≤ b
    simp
#align foobar foobar

theorem foo (I : Ideal R) (N : Submodule R M) :
    (N.map <| Submodule.mkQ (I • (⊤ : Submodule R M))).map (Submodule.idqₛₗ M I) =
      N.map (Submodule.mkqₛₗ M I) :=
  by
  apply SetLike.coe_injective
  change id '' _ = _
  simp
  rfl
#align foo foo

open Ideal

theorem generate_of_quotient_generate_of_le_jacobson (I : Ideal R) (hM : (⊤ : Submodule R M).FG)
    (hIjac : I ≤ jacobson ⊥) (N : Submodule R M) (hIM : Submodule.map (Submodule.mkqₛₗ M I) N = ⊤) :
    N = (⊤ : Submodule R M) := by
  let MM : Submodule R M := ⊤
  suffices hh : N ⊔ I • MM = MM
  · have nak : I • MM ≤ N :=
      by
      apply Submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot hM hIjac _
      simpa only [eq_self_iff_true, sup_top_eq, top_le_iff]
    rw [show N = N ⊔ I • MM by simp [nak], hh]
  rw [sup_comm, ← Submodule.map_mkQ_eq_top (I • MM) N]
  apply_fun foobar _ _
  · rw [OrderIso.map_top]
    convert hIM
    dsimp
    rw [foo]
  · apply OrderIso.injective
#align generate_of_quotient_generate_of_le_jacobson generate_of_quotient_generate_of_le_jacobson

