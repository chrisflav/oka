/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# A submodule of a presheaf of modules, as a subfunctor of the underlying presheaf of types

Material for `Mathlib/Algebra/Category/ModuleCat/Presheaf/Submodule.lean`; see `README.md` on the
mirror tree. That file does not currently import `Mathlib.CategoryTheory.Subfunctor.Basic`, which
the definition below names, so upstreaming it adds that import — **one** file to the target's own
transitive closure, measured rather than estimated.

`PresheafOfModules.Submodule` is a submodule of `M.obj X` for each object `X`, closed under the
restriction maps. `PresheafOfModules.Submodule.toSubfunctor` forgets the module structure and
reads the same data as a `CategoryTheory.Subfunctor` of the underlying type-valued presheaf. That
is the form the descent API is stated in: `CategoryTheory.Subfunctor.sieveOfSection` and
`CategoryTheory.Subfunctor.isSheaf_iff` are what
`Oka/Algebra/Category/ModuleCat/Sheaf/Submodule.lean` — this file's only consumer — uses to say
when a submodule of a sheaf of modules is itself a sheaf.

The `simp` lemma beside it says that membership in the subfunctor is membership in the submodule.
It is `Iff.rfl`, and it exists so that `simp` can cross the forgetful functor rather than because
it has content.

## Main definitions

- `PresheafOfModules.Submodule.toSubfunctor`
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

namespace Submodule

variable {M : PresheafOfModules.{v} R} (N : M.Submodule)

/-- The subfunctor of the underlying type-valued presheaf of `M` induced by a submodule `N`. -/
def toSubfunctor : Subfunctor (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) where
  obj X := {r : M.obj X | r ∈ N.obj X}
  map := fun {_ _} f _ hr ↦ N.map_mem f hr

/-- Membership in the subfunctor is membership in the submodule. This is `Iff.rfl`; see the
module docstring for why it is a `simp` lemma. -/
@[simp]
lemma mem_toSubfunctor_obj {X : Cᵒᵖ} (r : M.obj X) :
    r ∈ N.toSubfunctor.obj X ↔ r ∈ N.obj X := Iff.rfl

end Submodule

end PresheafOfModules
