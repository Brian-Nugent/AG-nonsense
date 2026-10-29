/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local properties of presheaves and sheaves

Additions from `Brian-Nugent/mathlib4` at commit
`aa5bcdad6bf59fc419495240ce8a4a5a07abba06` (`Pic`), kept outside the mathlib dependency.

In this file we study properties of presheaves and sheaves that can be checked on a covering
family of objects.

- `CategoryTheory.GrothendieckTopology.W_of_isIso_of_coversTop`: A morphism of presheaves
  becomes an isomorphism after sheafification if it is one on a cover.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

variable {C : Type*} [Category* C] {K : GrothendieckTopology C} {A : Type*} [Category* A]

section Concrete

variable {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  {ι : Type*} {X : ι → C} {F G : Cᵒᵖ ⥤ A}

namespace Presheaf

/-- A morphism of presheaves is locally injective if its components are injective
on objects lying over a covering family. -/
lemma isLocallyInjective_of_coversTop (hX : K.CoversTop X) (f : F ⟶ G)
    (h : ∀ i (Y : C) (_ : Y ⟶ X i), Function.Injective (f.app (op Y))) :
    IsLocallyInjective K f where
  equalizerSieve_mem {Y} x y hxy := by
    refine K.superset_covering ?_ (hX Y.unop)
    rintro Z g ⟨i, ⟨a⟩⟩
    apply h i Z a
    simpa only [NatTrans.naturality_apply] using congrArg (G.map g.op) hxy

/-- A morphism of presheaves is locally surjective if its components are surjective
on objects lying over a covering family. -/
lemma isLocallySurjective_of_coversTop (hX : K.CoversTop X) (f : F ⟶ G)
    (h : ∀ i (Y : C) (_ : Y ⟶ X i), Function.Surjective (f.app (op Y))) :
    IsLocallySurjective K f where
  imageSieve_mem {Y} s := by
    refine K.superset_covering ?_ (hX Y)
    rintro Z g ⟨i, ⟨a⟩⟩
    exact h i Z a (G.map g.op s)

end Presheaf

/-- A morphism of presheaves becomes an isomorphism after sheafification if its
components are isomorphisms on objects lying over a covering family. -/
lemma GrothendieckTopology.W_of_isIso_of_coversTop [K.WEqualsLocallyBijective A]
    (hX : K.CoversTop X) (f : F ⟶ G)
    (h : ∀ i (Y : C) (_ : Y ⟶ X i), IsIso (f.app (op Y))) : K.W f := by
  have : Presheaf.IsLocallyInjective K f :=
    Presheaf.isLocallyInjective_of_coversTop hX f fun i Y a => by
      have := h i Y a
      exact (ConcreteCategory.bijective_of_isIso (f.app (op Y))).injective
  have : Presheaf.IsLocallySurjective K f :=
    Presheaf.isLocallySurjective_of_coversTop hX f fun i Y a => by
      have := h i Y a
      exact (ConcreteCategory.bijective_of_isIso (f.app (op Y))).surjective
  exact K.W_of_isLocallyBijective f

end Concrete

end CategoryTheory
