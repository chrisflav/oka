/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.Sigma

/-!
# The trivial `n`-sheeted cover of a complex analytic space

`ComplexAnalytic.AnalyticSpace.sigmaDesc` is the morphism out of a disjoint union determined by a
morphism out of each member. This file says that being **finite** and being a **local
isomorphism** both pass from the members to it, and applies that to the family of `n` copies of a
single space mapping to it by the identity.

**That morphism realises every number of sheets**:
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` gives every value at once. It is also the
first `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` witness with a **disconnected source**, which
is the local model of *evenly covered* and the shape the analytic side of the Riemann existence
theorem is stated in.

## There is no analysis in any of it

Every proof below is topology and category theory. The two conditions are checked against
`AlgebraicGeometry.LocallyRingedSpace`-level statements in
`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean` —
`AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc`,
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`,
`AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc` and
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc` — which is where they belong,
since none of them mentions anything complex-analytic. What is left here is the translation
across `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` and the counting.

## The fibre is an equivalence and not a cardinality, and that is what makes `n = 0` free

`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv` exhibits the fibre of a descent map as
`Σ i, (fibre of the i-th piece)`. Finiteness of the fibre and its size are then the same object
read twice, and neither statement needs a positivity hypothesis on the index type.

**`n = 0` is a real case and this file admits it rather than excluding it.** The coproduct of the
empty family is the empty analytic space (`ComplexAnalytic.AnalyticSpace.isEmpty_sigma`), and the
empty space over a non-empty one is **finite étale here**: the underlying map is closed because
every image is empty, its fibres are empty and hence finite, and it is a local homeomorphism and
an isomorphism on stalks because it has no points to check either at.
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` then reads `0 = 0`.

That is a decision and not a theorem about the classical notion: **some definitions of a covering
map require surjectivity**, and under those the empty cover of a non-empty base is not one.
`ComplexAnalytic.AnalyticSpace.IsFinite` and `ComplexAnalytic.AnalyticSpace.IsLocalIso` as
`Oka/AnalyticSpace/Finite.lean` and `Oka/AnalyticSpace/LocalIso.lean` state them do not, and
neither does Mathlib's `IsCoveringMap`, whose evenly-covered condition is satisfied at every point
by the empty index type — `Oka/AnalyticSpace/CoveringMap.lean` says so in terms. So this file
inherits the convention rather than choosing it, and the value of
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` at `n = 0` is what that convention commits
one to. It is stated here so that a reader who expected `0 < n` finds the answer rather than a
missing hypothesis.

## What is not here

**The `degree` function is not here, and it is no longer absent from the development.**
`ComplexAnalytic.AnalyticSpace.degree` is in `Oka/AnalyticSpace/Degree.lean`, which imports this
file and reads `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` into
`ComplexAnalytic.AnalyticSpace.degree_sigmaFold`; the paragraph that used to stand here quoted
`Oka/AnalyticSpace/LocalIso.lean` declining a degree, and that refusal has been withdrawn there.
What is true of *this* file is unchanged and is why the direction of the import is that way round:
the count below is computed at every point directly, so
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` is not used and no connectedness
hypothesis appears.

**The one-sheeted case is settled and it cost no sheaf argument.** This paragraph said that for
`n = 1` the fold map is a bijection on points, that one would expect it to be an isomorphism, and
that *"that is a statement about the structure sheaves as well and nothing here proves it"*.
`ComplexAnalytic.AnalyticSpace.isIso_sigmaFold` proves it and reads no structure sheaf: the
inclusion of the single member is a two-sided inverse by the universal property of the disjoint
union, so the recorded obstruction named the wrong thing. **What is still not here is any claim
that a trivial cover is not a non-trivial one at more than one sheet** — that is a statement about
an invariant, and `Oka/AnalyticSpace/FiniteEtaleOver.lean` is where the two invariants this
development has for it are read off an object.

**Nothing about the analytification of a finite étale morphism of schemes**, which is the other
blocker of the Riemann existence theorem and is untouched.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.sigmaFold`: **the trivial `ι`-sheeted cover** `∐_{i : ι} X ⟶ X`,
  the descent map of the constant family at the identity.
- `ComplexAnalytic.AnalyticSpace.sigmaFoldIso`: **it, at one sheet, as an isomorphism onto the
  base**.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc` and
  `ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc`: **finiteness and being a local
  isomorphism pass from the members of a disjoint union to a descent map out of it**, the first
  for a finite index type and the second for any.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc`: the two together.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`: **the trivial `ι`-sheeted cover is
  finite étale** for a finite `ι`.
- `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold`: **every fibre of it has `Nat.card ι`
  points**, at every point of the base and with no connectedness hypothesis.
- `ComplexAnalytic.AnalyticSpace.isIso_sigmaFold`: **at one sheet it is an isomorphism**, by the
  universal property and with no structure sheaf read — which is the case
  `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` puts at one point per fibre and says
  nothing more about.
- `ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base` and
  `ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base`: **the image of a member of a
  disjoint union is closed**, and so clopen — the members are disjoint, so one image's complement
  is a union of the others'.
- `ComplexAnalytic.AnalyticSpace.sigmaιOpens`: **that image as a bundled open**, with
  `ComplexAnalytic.AnalyticSpace.coe_sigmaιOpens` for its carrier and
  `ComplexAnalytic.AnalyticSpace.isClosed_sigmaιOpens` for the closedness in the spelling a
  restriction to a clopen part asks for.
- `ComplexAnalytic.AnalyticSpace.sigmaιOpens_ne_bot` and
  `ComplexAnalytic.AnalyticSpace.sigmaιOpens_ne_top`: **that open is neither `⊥` nor `⊤`**, given
  a point of the member and a point of a different one — so it is a proper clopen part, which is
  what makes restricting a cover to one say anything.
- `ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma`: **a disjoint union with two
  distinct inhabited members is not preconnected**, which is the clopen image read as a
  separation.
- `ComplexAnalytic.AnalyticSpace.isFinite_sigmaι`,
  `ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaι` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι`: **the inclusion of a member is finite, a
  local isomorphism, and finite étale**, for every family and with no hypothesis on the other
  members and none on the index type.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.LocallyRingedSpace TopologicalSpace Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

variable {ι : Type u} (F : ι → AnalyticSpace.{u}) {Y : AnalyticSpace.{u}} (g : ∀ i, F i ⟶ Y)

/-- **The underlying morphism of a descent map is the coproduct's descent map.**

`ComplexAnalytic.AnalyticSpace.sigmaDesc` is built with `CategoryTheory.Limits.Sigma.desc` as its
`toLRSHom'` field, so this is `rfl`. **It is stated for a reader and for a consumer that does not
exist yet, not because anything below needs it**: the statements below reach the
locally-ringed-space lemmas by definitional unfolding, since the field really is `Sigma.desc`, and
this file compiles with the lemma deleted. Its `@[simp]` cannot fire here either, there being no
`simp` call in the file. Measured 2026-08-25 at `master` = `d12d334`; an earlier version of this
docstring said the two spellings are different discrimination-tree keys and that every statement
below applies a locally-ringed-space lemma *to this lemma*, which is not what the proofs do. -/
@[simp]
lemma toLRSHom_sigmaDesc : (sigmaDesc F g).toLRSHom = Sigma.desc fun i ↦ (g i).toLRSHom := rfl

/-- **A descent map out of a disjoint union of finitely many analytic spaces is finite as soon as
each of its restrictions is.**

The closed half is
`AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc` and the fibre half is
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`, which presents the fibre as
`Σ i, (fibre of the i-th piece)` — so its finiteness is `Finite.instSigma` and needs the index
type finite for the second time.

**`[Finite ι]` is used twice and for two different reasons**: once to make the union of the
members' images a finite union of closed sets, and once to make the fibre a finite disjoint
union. Neither use is removable and the two are independent. -/
instance isFinite_sigmaDesc [Finite ι] [∀ i, IsFinite (g i)] : IsFinite (sigmaDesc F g) where
  isClosedMap := isClosedMap_base_sigmaDesc _ _ fun i ↦ IsFinite.isClosedMap (f := g i)
  finite_fiber y := by
    have hi : ∀ i, Finite (((g i).toLRSHom.base ⁻¹' {y} : Set (F i))) :=
      fun i ↦ IsFinite.finite_fiber (f := g i) y
    exact @Finite.of_equiv _ _ (@Finite.instSigma _ _ _ hi)
      (fiberSigmaDescEquiv (fun i ↦ (F i).toLocallyRingedSpace) (fun i ↦ (g i).toLRSHom) y)

/-- **A descent map out of a disjoint union is a local isomorphism as soon as each of its
restrictions is**, with no finiteness hypothesis on the index type.

The two fields are `AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc` and
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc`, and the reason neither needs
`[Finite ι]` is the same in both cases: both are conditions **at a point**, and a point of the
coproduct lies in exactly one member.

Note the asymmetry with `ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc`, which is not an
artefact of the proofs: an infinite disjoint union of copies of a space really is a local
isomorphism over it and really is not finite over it, since the fibres are infinite. -/
instance isLocalIso_sigmaDesc [∀ i, IsLocalIso (g i)] : IsLocalIso (sigmaDesc F g) where
  isLocalHomeomorph :=
    isLocalHomeomorph_base_sigmaDesc _ _ fun i ↦ IsLocalIso.isLocalHomeomorph (f := g i)
  isIso_stalkMap x :=
    isIso_stalkMap_sigmaDesc _ _ (fun i z ↦ IsLocalIso.isIso_stalkMap (f := g i) z) x

/-- **A descent map out of a disjoint union of finitely many members is finite étale as soon as
each of its restrictions is**, from the two rungs above and nothing else. -/
instance isFiniteEtale_sigmaDesc [Finite ι] [∀ i, IsFiniteEtale (g i)] :
    IsFiniteEtale (sigmaDesc F g) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-! ### The inclusions -/

/-- **The image of a member of a disjoint union is closed**, and not merely open.

The members are pairwise disjoint, so the complement of one image is the union of the others' —
a union of opens. `AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq` places an
arbitrary point of the coproduct in *some* member and
`AlgebraicGeometry.LocallyRingedSpace.disjoint_range_sigmaι` keeps it out of this one; the image
being open is `AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion`.

**This is what `ComplexAnalytic.AnalyticSpace.isFinite_sigmaι` takes from the coproduct**, and
through it `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι`;
`ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaι` uses none of it — both of its fields are the
inclusion being an *open* immersion, as its own docstring below records. It is worth naming on
its own: *clopen*, and not
*open*, is what an inclusion of a member is.

`AlgebraicGeometry.LocallyRingedSpace.disjoint_range_sigmaι _ hij` at `hij : i ≠ j` is already
`Disjoint (Set.range (Sigma.ι f i).base) (Set.range (Sigma.ι f j).base)` in that order; adding a
`.symm` to fit `Set.subset_compl_iff_disjoint_right` is the wrong way round, and the error names
two ranges that print almost identically. -/
theorem isClosed_range_sigmaι_base (j : ι) :
    IsClosed (Set.range (sigmaι F j).toLRSHom.base) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, y, hy⟩ := exists_sigma_ι_base_eq (fun i ↦ (F i).toLocallyRingedSpace) x
  have hij : i ≠ j := by rintro rfl; exact hx ⟨y, hy⟩
  refine ⟨Set.range (Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) i).base, ?_, ?_, ⟨y, hy⟩⟩
  · rw [Set.subset_compl_iff_disjoint_right]
    exact disjoint_range_sigmaι _ hij
  · exact (sigmaι_isOpenImmersion _ i).base_open.isOpen_range

/-- **The image of a member of a disjoint union is clopen.**

The word the theorem above argues for and does not spell: its own statement paired with the
inclusion being an *open* immersion,
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion`. Nothing is proved here that is not
already proved above, and it is a separate name because `IsClopen` is the hypothesis
`isClopen_iff` wants and a caller assembling the pair at each use site is the shape that goes
stale.

**`IsClopen` is a conjunction and not a structure, and the consumer below is written the way it
is because of that.** `IsClopen s` reduces to `IsClosed s ∧ IsOpen s`, so this term is an
anonymous constructor and, in the other direction, `(isClopen_range_sigmaι_base F i).…` projects
fields of `And` — an `eq_empty_or_univ` reached that way resolves against `And` and does not
exist, and Mathlib spells the step as the standalone `isClopen_iff`, which is what the proof below
calls. Measured here, both spellings. -/
theorem isClopen_range_sigmaι_base (j : ι) :
    IsClopen (Set.range (sigmaι F j).toLRSHom.base) :=
  ⟨isClosed_range_sigmaι_base F j,
    (sigmaι_isOpenImmersion (fun i ↦ (F i).toLocallyRingedSpace) j).base_open.isOpen_range⟩

/-- **The image of a member of a disjoint union, as an open of the disjoint union.**

`ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base` proves the carrier is clopen; this
carries it as a bundled `TopologicalSpace.Opens`, which is the type a restriction consumes.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` asks for an
`Opens` of the total space together with a proof that its coercion is closed, and the clopen
lemma hands back a bare `Set` and a conjunction — so without this a caller has to build the
bundled open at each use site, which is the shape
`ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base` already declines to leave to a caller.

**Only the openness half is consumed here.** The closedness travels separately, as
`ComplexAnalytic.AnalyticSpace.isClosed_sigmaιOpens`, because it is a hypothesis of the
restriction rather than part of its subject. -/
def sigmaιOpens (j : ι) : (sigma F).Opens :=
  ⟨Set.range (sigmaι F j).toLRSHom.base, (isClopen_range_sigmaι_base F j).2⟩

/-- The carrier of `ComplexAnalytic.AnalyticSpace.sigmaιOpens`. -/
@[simp]
lemma coe_sigmaιOpens (j : ι) :
    ((sigmaιOpens F j : (sigma F).Opens) : Set (sigma F))
      = Set.range (sigmaι F j).toLRSHom.base :=
  rfl

/-- **The member image, read off the bundled open, is closed.**

`ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base` says the same thing about
`Set.range (sigmaι F j).toLRSHom.base`, and the two are `rfl`-equal.

**This is a convenience and not a necessity, and an earlier draft of this paragraph claimed the
second.** That draft argued that the coercion of the bundled open and the bare range are different
discrimination-tree keys, which they are — but
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` takes the closedness as an
**explicit argument**, so all that is ever asked of it is `exact`-level definitional equality, and
`ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base` discharges the bundled statement
directly. Discrimination-tree keys govern `simp` and instance search, and neither runs here. What
this name buys is that the subject of the statement is the open a caller is holding. -/
theorem isClosed_sigmaιOpens (j : ι) :
    IsClosed ((sigmaιOpens F j : (sigma F).Opens) : Set (sigma F)) :=
  (isClopen_range_sigmaι_base F j).1

/-- **A member's image is not the empty open**, as soon as that member has a point.

The point is all that is asked: no hypothesis on the index type, and none on the other members.
Without it the statement is false, an empty member having empty image. -/
theorem sigmaιOpens_ne_bot {j : ι} (x : F j) : sigmaιOpens F j ≠ ⊥ := by
  intro h
  have hx : (sigmaι F j).toLRSHom.base x ∈ (sigmaιOpens F j : Set (sigma F)) :=
    Set.mem_range_self x
  rw [h] at hx
  exact hx

/-- **A member's image is not everything**, as soon as a *different* member has a point.

`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq` is what turns *"the point's image
lies in the `j`-th member's image"* into `i = j`, which the hypothesis then refutes.
`ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma` asks for the hypotheses stated here
and for a point of `F j` besides, and it asks for `i ≠ j` and a point of `F i` for the reason
given here: at a one-member family, or at one whose other members are empty, the disjoint union
**is** the member and its image really is everything.

**Together with `ComplexAnalytic.AnalyticSpace.sigmaιOpens_ne_bot` this is what makes a
restriction to a clopen part say something.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` accepts `⊥` and `⊤` as readily as
anything else, so a cover restricted to a clopen part is only informative at a clopen part that
is neither, and this pair is what exhibits one. -/
theorem sigmaιOpens_ne_top {i j : ι} (hij : i ≠ j) (y : F i) : sigmaιOpens F j ≠ ⊤ := by
  intro h
  have hy : (sigmaι F i).toLRSHom.base y ∈ (sigmaιOpens F j : Set (sigma F)) := by
    rw [h]; trivial
  obtain ⟨z, hz⟩ := hy
  exact hij (eq_of_sigmaι_base_eq _ hz).symm

/-- **A disjoint union with two distinct inhabited members is not preconnected.**

The image of the `i`-th member is clopen by
`ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base`, so over a preconnected space it is
empty or everything (`isClopen_iff`); the point `x` keeps it from being empty and the point `y`,
in a *different* member, keeps it from being everything —
`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq` is what turns *"`y`'s image is in the
`i`-th member's image"* into `i = j`.

**Both hypotheses are needed and neither is decorative.** At a one-member family, or at a family
whose other members are empty, the disjoint union *is* the member and can perfectly well be
preconnected — `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`
(`Oka/AnalyticSpace/Sigma.lean`) is the same pair of hypotheses for the same reason, and the
empty disjoint union of `ComplexAnalytic.AnalyticSpace.isEmpty_sigma` is preconnected vacuously.

**The other `¬ PreconnectedSpace` statement here is narrower than this one.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial`
(`Oka/AnalyticSpace/FiniteEtaleOver.lean`) is this theorem read at the constant family. **This is
about every disjoint union at once**, and it is what `Oka/AnalyticSpace/FiniteEtaleOver.lean`
reads to separate a connected cover from a trivial one of the same degree. Note which way round
the file's headline runs:
`ComplexAnalytic.AnalyticSpace.sigmaFold` was already called *"the first `IsFiniteEtale` witness
with a disconnected source"* in the module docstring above — **an assertion this theorem is the
first proof of.** -/
theorem not_preconnectedSpace_sigma {i j : ι} (hij : i ≠ j) (x : F i) (y : F j) :
    ¬ PreconnectedSpace (sigma F) := by
  intro _
  rcases isClopen_iff.mp (isClopen_range_sigmaι_base F i) with he | hu
  · exact (he ▸ Set.mem_range_self x : ((sigmaι F i).toLRSHom.base x) ∈ (∅ : Set (sigma F)))
  · obtain ⟨z, hz⟩ : ((sigmaι F j).toLRSHom.base y) ∈
        Set.range ((sigmaι F i).toLRSHom.base : F i → sigma F) := hu ▸ Set.mem_univ _
    exact hij (eq_of_sigmaι_base_eq _ hz)

/-- **The inclusion of a member of a disjoint union is finite**, for every family and with no
hypothesis on the other members.

`ComplexAnalytic.AnalyticSpace.IsFinite` is a closed base map and finite fibres and nothing else.
The first is a closed embedding — an open embedding by
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion` with closed range by the theorem
above — and the second is that an injective map has subsingleton fibres, injectivity being
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_injective`.

**An `instance` rather than a `theorem`, and the choice is deliberate.** Its head is
`ComplexAnalytic.AnalyticSpace.sigmaι`, which no other instance on this line produces, so it
fires only on a goal that already names an inclusion and cannot chain;
`ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc` and
`ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc` are instances for the same reason. -/
instance isFinite_sigmaι (j : ι) : IsFinite (sigmaι F j) where
  isClosedMap :=
    (IsClosedEmbedding.mk
      (sigmaι_isOpenImmersion (fun i ↦ (F i).toLocallyRingedSpace) j).base_open.isEmbedding
      (isClosed_range_sigmaι_base F j)).isClosedMap
  finite_fiber y := by
    have hsub : ((sigmaι F j).toLRSHom.base ⁻¹' {y}).Subsingleton := fun a ha b hb ↦
      sigmaι_base_injective (fun i ↦ (F i).toLocallyRingedSpace) j (ha.trans hb.symm)
    exact hsub.finite.to_subtype

/-- **The inclusion of a member of a disjoint union is a local isomorphism**, for every family.

Both fields are the inclusion being an open immersion:
`Topology.IsOpenEmbedding.isLocalHomeomorph` for the base and
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.stalk_iso` for the stalks. **Neither is
about the coproduct**; the same two lines prove it for any open immersion, and what is particular
here is only that the inclusion is one.

**The point has to be retyped before the stalk instance is found.** `x` arrives as a point of the
analytic space `F j` and the instance is indexed on a point of `(F j).toLocallyRingedSpace`; the
two are definitionally equal and instance search is syntactic, so `inferInstanceAs` at the second
spelling is what fires. Without it the goal reports `failed to synthesize IsIso …` with a term
that prints identically to one that does synthesise. -/
instance isLocalIso_sigmaι (j : ι) : IsLocalIso (sigmaι F j) where
  isLocalHomeomorph := by
    rw [sigmaι_toLRSHom]
    exact (sigmaι_isOpenImmersion
      (fun i ↦ (F i).toLocallyRingedSpace) j).base_open.isLocalHomeomorph
  isIso_stalkMap x := by
    rw [sigmaι_toLRSHom]
    exact inferInstanceAs (IsIso ((Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) j).stalkMap
      (x : (F j).toLocallyRingedSpace)))

/-- **The inclusion of a member of a disjoint union is finite étale**, for every family, from the
two rungs above and nothing else.

**No `[Finite ι]`**, unlike `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc`: the fibres of
an inclusion are subsingletons whatever the index type is, and the closedness of its image is a
complement of a *single* union of opens rather than a finite union of closed sets. The asymmetry
is real and is the same one `ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc`'s docstring
records from the other side. -/
instance isFiniteEtale_sigmaι (j : ι) : IsFiniteEtale (sigmaι F j) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-! ### The trivial cover -/

variable (ι) in
/-- **The trivial `ι`-sheeted cover of an analytic space**: `∐_{i : ι} X ⟶ X`, the descent map of
the constant family at the identity of `X`.

This is the fold map of the coproduct, and it is a cover in the honest sense as soon as `ι` is
finite: `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`. The index type is a `Type u` and
not a `ℕ` because `ComplexAnalytic.AnalyticSpace.sigma` is indexed by one; the `n`-sheeted cover
is this at `ULift (Fin n)`. -/
def sigmaFold (X : AnalyticSpace.{u}) : sigma (fun _ : ι ↦ X) ⟶ X :=
  sigmaDesc _ fun _ ↦ 𝟙 X

/-- **The trivial `ι`-sheeted cover is finite étale**, for a finite index type.

`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc` at the constant family, whose pieces are
identities and are finite étale by `ComplexAnalytic.AnalyticSpace.isFiniteEtale_id`. Nothing is
asked of `X` — not Hausdorff, not connected, not non-empty. -/
instance isFiniteEtale_sigmaFold [Finite ι] (X : AnalyticSpace.{u}) :
    IsFiniteEtale (sigmaFold ι X) where
  isFinite := isFinite_sigmaDesc _ _
  isLocalIso := isLocalIso_sigmaDesc _ _

/-- **Every fibre of the trivial `ι`-sheeted cover has `Nat.card ι` points.**

The composite of two equivalences: `AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`
presents the fibre as `Σ i : ι, ((𝟙 X).base ⁻¹' {x})`, and each of those fibres is the singleton
`{x}`, so `Equiv.sigmaUnique` collapses the sum to `ι`.

**`Nat.card` is not a junk value here even for an infinite `ι`, and it is not informative either.**
For infinite `ι` both sides are `0` — the fibre is infinite and `Nat.card` of an infinite type is
`0` — so the statement is true but says nothing; it is `[Finite ι]`-free because the proof is, not
because the content survives. The morphism is not finite étale in that case, so nothing downstream
reads it there.

Unlike `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, which says the number is
*constant* over a preconnected base, this computes it at each point separately and needs no
hypothesis on `X` at all. -/
theorem card_fiber_sigmaFold (X : AnalyticSpace.{u}) (x : X) :
    Nat.card ((sigmaFold ι X).toLRSHom.base ⁻¹' {x}) = Nat.card ι := by
  have hu : ∀ _ : ι, Unique (((𝟙 X : X ⟶ X).toLRSHom.base ⁻¹' {x} : Set X)) := by
    intro _
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
    rw [h, Set.preimage_id]
    infer_instance
  refine (Nat.card_eq_of_bijective _
    (fiberSigmaDescEquiv (fun _ : ι ↦ X.toLocallyRingedSpace)
      (fun _ ↦ (𝟙 X : X ⟶ X).toLRSHom) x).symm.bijective).trans ?_
  exact Nat.card_eq_of_bijective _ (@Equiv.sigmaUnique ι _ hu).bijective

/-- **The fold map restricts to the identity on each member**, which is
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` at the constant family and is stated because
`ComplexAnalytic.AnalyticSpace.sigmaFold` is a `def`: `simp` does not unfold it to reach the
descent map underneath, so the general lemma does not fire on this composite. -/
@[simp]
theorem sigmaι_sigmaFold {ι : Type u} (X : AnalyticSpace.{u}) (j : ι) :
    sigmaι (fun _ : ι ↦ X) j ≫ sigmaFold ι X = 𝟙 X :=
  sigmaι_sigmaDesc _ _ j

variable (ι) in
/-- **At one sheet the trivial cover is an isomorphism**, so its total space is `X` and not merely
a space with the same points.

**This is what `## What is not here` recorded as absent, and the price recorded there is not what
it costs.** That paragraph said the fold map is a bijection on points at one sheet, that one would
expect it to be an isomorphism, and that *"that is a statement about the structure sheaves as well
and nothing here proves it"*. No structure sheaf is touched: the inclusion of the single member is
a two-sided inverse by the universal property, so this is
`ComplexAnalytic.AnalyticSpace.isIso_sigmaι` (`Oka/AnalyticSpace/Sigma.lean`) read through
`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaFold` and two-out-of-three.

**`[Nonempty ι]` and `[Subsingleton ι]` rather than `[Unique ι]`**, which are the same class of
index types: the two instances are what the proof consumes, `Unique` is a structure carrying a
chosen point that nothing here reads, and a caller holding `Nat.card ι = 1` produces the pair
directly. The empty case is genuinely excluded and is not an oversight —
`ComplexAnalytic.AnalyticSpace.isEmpty_sigma` makes the source empty there, and the fold map out
of it is not an isomorphism over an inhabited `X`. -/
instance isIso_sigmaFold [Nonempty ι] [Subsingleton ι] (X : AnalyticSpace.{u}) :
    IsIso (sigmaFold ι X) := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  haveI : IsIso (sigmaι (fun _ : ι ↦ X) j ≫ sigmaFold ι X) := by
    rw [sigmaι_sigmaFold]; infer_instance
  exact IsIso.of_isIso_comp_left (sigmaι (fun _ : ι ↦ X) j) (sigmaFold ι X)

variable (ι) in
/-- **The one-sheeted disjoint union, as an isomorphism onto the base.**

`ComplexAnalytic.AnalyticSpace.isIso_sigmaFold` packaged by `CategoryTheory.asIso`, so that a
consumer wanting an isomorphism of objects rather than a property of a morphism has one to hand;
`Oka/AnalyticSpace/FiniteEtaleOver.lean` is that consumer. -/
def sigmaFoldIso [Nonempty ι] [Subsingleton ι] (X : AnalyticSpace.{u}) :
    sigma (fun _ : ι ↦ X) ≅ X :=
  asIso (sigmaFold ι X)

@[simp]
theorem sigmaFoldIso_hom {ι : Type u} [Nonempty ι] [Subsingleton ι] (X : AnalyticSpace.{u}) :
    (sigmaFoldIso ι X).hom = sigmaFold ι X :=
  rfl

end

end ComplexAnalytic.AnalyticSpace
