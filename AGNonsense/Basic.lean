/-
Copyright (c) 2026 AG-nonsense contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AG-nonsense contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Algebraic geometry playground

Add algebraic geometry results here, or create more focused modules under `AGNonsense/`.
The example below checks that mathlib's category of schemes is available.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

example (X : Scheme) : X ⟶ X := 𝟙 X

end AlgebraicGeometry
