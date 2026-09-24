/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Composing a sheaf with a corepresentable forgetful functor

Material for `Mathlib/CategoryTheory/Sites/Whiskering.lean`; see `README.md` on the mirror tree.
This file imports its target and nothing else, so upstreaming it adds nothing to that file's
transitive imports.

`CategoryTheory.GrothendieckTopology.HasSheafCompose F` says that composing a sheaf with `F`
again yields a sheaf. Mathlib's file supplies two instances of it and both are keyed on `F`
preserving limits: `CategoryTheory.hasSheafCompose_of_preservesMulticospan` and
`CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize`. The instance below is keyed on the
forgetful functor of a concrete category being **corepresentable** instead, and its proof is a
transport rather than a limit argument: `CategoryTheory.Functor.coreprW` identifies `forget A`
with a hom-functor, and `CategoryTheory.Presieve.isSheaf_iso` moves the type-valued sheaf
condition across that isomorphism. Nothing here claims the hypotheses are independent of
Mathlib's; only that the route is different and shorter at this hypothesis.

**Nothing in this repository imports this file.** `Oka.lean`, which `lake exe mk_all` generates
and which lists every module of the library, is its only importer, so the instance is in scope
nowhere and is exercised by nothing here. That is recorded rather than acted on: it is a correct
statement about Mathlib's own types, it is upstreamable on its own, and whether to keep an
unexercised instance is not a question a module docstring should decide.

## Main declarations

- an instance of `CategoryTheory.GrothendieckTopology.HasSheafCompose` for the forgetful functor
  of a concrete category whose `CategoryTheory.Functor.IsCorepresentable` instance is available.
  It is anonymous and carries no docstring of its own.
-/

@[expose] public section

universe v u v₁ u₁

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {A : Type u} [Category.{v} A]
  {FA : A → A → Type*} {CA : A → Type v} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA] (J : GrothendieckTopology C)

instance [(forget A).IsCorepresentable] :
    J.HasSheafCompose (forget A) where
  isSheaf P hP := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso J (Functor.isoWhiskerLeft P (forget A).coreprW)
      (hP (forget A).coreprX)

end CategoryTheory
