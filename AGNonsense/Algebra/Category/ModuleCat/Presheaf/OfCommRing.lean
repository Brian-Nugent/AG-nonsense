/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import AGNonsense.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Forgetting presheaves of modules to abelian presheaves

Additions from `Brian-Nugent/mathlib4` at commit
`aa5bcdad6bf59fc419495240ce8a4a5a07abba06` (`Pic`), kept outside the mathlib dependency.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C]

/-- The forgetful functor to presheaves of abelian groups. -/
noncomputable abbrev toPresheaf (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModulesOfCommRing.{v} R ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  PresheafOfModules.toPresheaf (R ⋙ forget₂ _ _)

end PresheafOfModulesOfCommRing
