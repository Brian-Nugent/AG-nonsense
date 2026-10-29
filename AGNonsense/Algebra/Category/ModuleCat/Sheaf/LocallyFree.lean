/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Locally free sheaves of a specified rank

Additions from `Brian-Nugent/mathlib4` at commit
`aa5bcdad6bf59fc419495240ce8a4a5a07abba06` (`Pic`), kept outside the mathlib dependency.
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

noncomputable section

namespace SheafOfModules

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Local generator data `q` is locally free data of rank `n` if it is locally free and
each family of generators has cardinality `n`. -/
class IsLocallyFreeDataOfRank {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) (n : ℕ)
    extends q.IsLocallyFreeData, q.IsFiniteType where
  rank : ∀ i, Nat.card (q.generators i).I = n

/-- A local trivialization supplied by locally free data of rank one. -/
def isoUnit {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeDataOfRank 1] (i : q.I) :
    M.over (q.X i) ≅ unit (R.over (q.X i)) := by
  obtain ⟨h, h'⟩ := Nat.card_eq_one_iff_unique.mp (IsLocallyFreeDataOfRank.rank (q := q) i)
  letI := Classical.choice (nonempty_unique (q.generators i).I)
  exact (asIso (q.generators i).π).symm ≪≫ coproductUniqueIso _

instance IsLocallyFreeDataOfRank.shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    (n : ℕ) [q.IsLocallyFreeDataOfRank n] : q.shrink.IsLocallyFreeDataOfRank n where
  isFiniteType i := IsFiniteType.isFiniteType i.2.choose
  rank i := IsLocallyFreeDataOfRank.rank i.2.choose

end LocalGeneratorsData

/-- A sheaf of modules is locally free of rank `n` if it is locally isomorphic to a free
sheaf of rank `n` -/
class IsLocallyFreeOfRank (M : SheafOfModules.{u} R) (n : semiOutParam ℕ) : Prop where
  exists_isLocallyFreeDataOfRank : ∃ q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeDataOfRank n

instance (M : SheafOfModules.{u} R) (n : ℕ) [M.IsLocallyFreeOfRank n] :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := IsLocallyFreeOfRank.exists_isLocallyFreeDataOfRank (M := M) (n := n)
  exact ⟨⟨q, inferInstance⟩⟩

instance (M : SheafOfModules.{u} R) (n : ℕ) [M.IsLocallyFreeOfRank n] :
    M.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsLocallyFreeOfRank.exists_isLocallyFreeDataOfRank (M := M) (n := n)
  exact ⟨⟨q, inferInstance⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf of modules is locally free of rank one if it is isomorphic to the unit
over a family of objects covering the terminal object. -/
theorem isLocallyFreeOfRank_one_of_coversTop {M : SheafOfModules.{u} R}
    {I : Type*} {U : I → C} (h : J.CoversTop U)
    (e : ∀ i, M.over (U i) ≅ unit (R.over (U i))) : M.IsLocallyFreeOfRank 1 := by
  let e' (i : I) : free PUnit.{u + 1} ≅ M.over (U i) :=
    coproductUniqueIso _ ≪≫ (e i).symm
  let q : M.LocalGeneratorsData :=
    { I := I
      X := U
      coversTop := h
      generators i := (free.generatingSections PUnit).ofEpi (e' i).hom }
  have : q.IsLocallyFreeDataOfRank 1 :=
    { isIso i := by
        change IsIso ((free.generatingSections PUnit).ofEpi _).π
        simp only [GeneratingSections.ofEpi_π, free.generatingSections_π]
        infer_instance
      isFiniteType i := ⟨inferInstanceAs (Finite PUnit)⟩
      rank i := by
        change Nat.card PUnit.{u + 1} = 1
        exact Nat.card_unique }
  exact ⟨q.shrink, inferInstance⟩

end SheafOfModules
