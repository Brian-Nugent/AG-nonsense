/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import AGNonsense.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import AGNonsense.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import AGNonsense.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import AGNonsense.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import AGNonsense.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import AGNonsense.Algebra.Category.ModuleCat.Sheaf.Invertible
public import AGNonsense.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import AGNonsense.Algebra.Category.ModuleCat.Sheaf.LocallyFreeOfInvertible
public import AGNonsense.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import AGNonsense.Algebra.Category.ModuleCat.Sheaf.OfCommRing
public import AGNonsense.Algebra.Category.ModuleCat.Sheaf.TensorTrivialization
public import AGNonsense.Algebra.Category.Ring.Sheaf.Local
public import AGNonsense.AlgebraicGeometry.Modules.Monoidal
public import AGNonsense.AlgebraicGeometry.Modules.Pic
public import AGNonsense.CategoryTheory.Monoidal.Closed.Basic
public import AGNonsense.CategoryTheory.Sites.LocalProperties
public import AGNonsense.Geometry.RingedSpace.IsLocallyRinged

/-!
# Additions from the mathlib Pic branch

Source: `Brian-Nugent/mathlib4`, branch `Pic`, commit `aa5bcdad6bf59fc419495240ce8a4a5a07abba06`.
The source branch is compared with its upstream merge base
`2f6ab85947289c79c86d3cd741583029b7629144`.

New modules are mirrored under `AGNonsense/`. Additions to existing mathlib
modules live in extension modules that import the unchanged upstream files.
The original `Mathlib.lean` import additions are represented by this module.
The three unfinished proofs in `Sheaf/Monoidal.lean` are inherited from `Pic`.
-/
