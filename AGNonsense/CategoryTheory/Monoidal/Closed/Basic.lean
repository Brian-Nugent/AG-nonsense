/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Isomorphisms and internal hom evaluation

Additions from `Brian-Nugent/mathlib4` at commit
`aa5bcdad6bf59fc419495240ce8a4a5a07abba06` (`Pic`), kept outside the mathlib dependency.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

namespace MonoidalClosed

instance [Closed (𝟙_ C)] : (ihom (𝟙_ C)).IsEquivalence :=
  Functor.isEquivalence_of_iso MonoidalClosed.unitNatIso

instance isIso_ihom_ev_unit [Closed (𝟙_ C)] : IsIso (ihom.ev (𝟙_ C)) :=
  inferInstanceAs (IsIso ((ihom.adjunction _).counit))

variable {A B : C} [Closed A] [Closed B]

instance (f : B ⟶ A) [IsIso f] : IsIso (pre f) :=
  inferInstanceAs (IsIso (conjugateEquiv _ _ _))

/-- Whether evaluation is an isomorphism is invariant under isomorphism of its source object. -/
lemma isIso_ihom_ev_app_iff_of_iso (e : A ≅ B) (X : C) :
    IsIso ((ihom.ev A).app X) ↔ IsIso ((ihom.ev B).app X) := by
  rw [← isIso_comp_left_iff (A ◁ (pre e.hom).app X),
    id_tensor_pre_app_comp_ev, isIso_comp_left_iff]

end MonoidalClosed

end CategoryTheory
