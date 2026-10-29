/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import AGNonsense.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import AGNonsense.CategoryTheory.Monoidal.Closed.Basic

/-!
# The universal property of the tensor product of presheaves of modules

Additions from `Brian-Nugent/mathlib4` at commit
`aa5bcdad6bf59fc419495240ce8a4a5a07abba06` (`Pic`), kept outside the mathlib dependency.

The universal property of this tensor product is given by
`PresheafOfModulesOfCommRing.tensorLift`: a family of bilinear maps compatible with
restriction induces a morphism from the tensor product. The lemma
`PresheafOfModulesOfCommRing.tensor_ext` gives uniqueness by testing on pure tensors.
-/

@[expose] public section

open CategoryTheory MonoidalCategory BraidedCategory Category Limits

universe u

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModulesOfCommRing

section TensorLift

variable {M₁ M₂ M₃ : PresheafOfModulesOfCommRing.{u} R}

/-- Morphisms out of a tensor product of presheaves of modules are determined by their
values on pure tensors. -/
lemma tensor_ext {f g : M₁ ⊗ M₂ ⟶ M₃}
    (h : ∀ (X : Cᵒᵖ) (m₁ : M₁.obj X) (m₂ : M₂.obj X),
      f.app X (m₁ ⊗ₜ[R.obj X] m₂) = g.app X (m₁ ⊗ₜ[R.obj X] m₂)) : f = g := by
  ext1 X
  exact ModuleCat.MonoidalCategory.tensor_ext (h X)

variable (f : ∀ (X : Cᵒᵖ), M₁.obj X → M₂.obj X → M₃.obj X)
  (hadd₁ : ∀ X m₁ m₁' m₂, f X (m₁ + m₁') m₂ = f X m₁ m₂ + f X m₁' m₂)
  (hsmul₁ : ∀ X (a : R.obj X) m₁ m₂, f X (a • m₁) m₂ = a • f X m₁ m₂)
  (hadd₂ : ∀ X m₁ m₂ m₂', f X m₁ (m₂ + m₂') = f X m₁ m₂ + f X m₁ m₂')
  (hsmul₂ : ∀ X (a : R.obj X) m₁ m₂, f X m₁ (a • m₂) = a • f X m₁ m₂)
  (hnat : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) m₁ m₂,
    f Y (M₁.map g m₁) (M₂.map g m₂) = M₃.map g (f X m₁ m₂))

/-- A family of bilinear maps compatible with restriction induces a morphism out of the
tensor product of two presheaves of modules. -/
noncomputable def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
  homMk (fun X ↦ ModuleCat.MonoidalCategory.tensorLift (f X)
    (hadd₁ X) (hsmul₁ X) (hadd₂ X) (hsmul₂ X)) (fun g ↦
      ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₂ ↦ hnat g m₁ m₂))

@[simp]
lemma tensorLift_app_tmul (X : Cᵒᵖ) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    (tensorLift f hadd₁ hsmul₁ hadd₂ hsmul₂ hnat).app X (m₁ ⊗ₜ[R.obj X] m₂) =
      f X m₁ m₂ := rfl

/-- The morphism induced by a compatible family of bilinear maps is unique. -/
lemma tensorLift_unique (g : M₁ ⊗ M₂ ⟶ M₃)
    (h : ∀ (X : Cᵒᵖ) (m₁ : M₁.obj X) (m₂ : M₂.obj X),
      g.app X (m₁ ⊗ₜ[R.obj X] m₂) = f X m₁ m₂) :
    g = tensorLift f hadd₁ hsmul₁ hadd₂ hsmul₂ hnat :=
  tensor_ext h

end TensorLift

end PresheafOfModulesOfCommRing
