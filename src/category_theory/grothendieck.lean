/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.category.Cat
import category_theory.eq_to_hom

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : F ⟶ (F.map (op β)).obj f'`.

## References

https://ncatlab.org/nlab/show/Grothendieck+construction

-/

universe u

open category_theory

variables {C D : Type*} [category C] [category D]
variables (F : C ⥤ Cat)

structure grothendieck :=
(base : C)
(fiber : F.obj base)

namespace grothendieck

variables {F}

structure hom (X Y : grothendieck F) :=
(base : X.base ⟶ Y.base)
(fiber : (F.map base).obj X.fiber ⟶ Y.fiber)

@[ext] lemma ext {X Y : grothendieck F} (f g : hom X Y)
  (w_base : f.base = g.base) (w_fiber : eq_to_hom (by rw w_base) ≫ f.fiber = g.fiber) : f = g :=
begin
  cases f; cases g,
  congr,
  dsimp at w_base,
  induction w_base,
  refl,
  dsimp at w_base,
  induction w_base,
  simpa using w_fiber,
end

@[simps]
def id (X : grothendieck F) : hom X X :=
{ base := 𝟙 X.base,
  fiber := eq_to_hom (by erw [category_theory.functor.map_id, functor.id_obj X.fiber]), }

@[simps]
def comp {X Y Z : grothendieck F} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ base := f.base ≫ g.base,
  fiber :=
  eq_to_hom (by erw [functor.map_comp, functor.comp_obj]) ≫
    (F.map g.base).map f.fiber ≫ g.fiber, }

end grothendieck

instance : category (grothendieck F) :=
{ hom := λ X Y, grothendieck.hom X Y,
  id := λ X, grothendieck.id X,
  comp := λ X Y Z f g, grothendieck.comp f g,
  comp_id' := λ X Y f,
  begin
    ext,
    { dsimp,
      -- We need to turn `F.map_id` (which is an equation between functors)
      -- into a natural isomorphism.
      rw ← nat_iso.naturality_2 (eq_to_iso (F.map_id Y.base)) f.fiber,
      simp,
      refl, },
    { simp, },
  end,
  id_comp' := λ X Y f, by ext; simp,
  assoc' := λ W X Y Z f g h,
  begin
    ext, swap,
    { simp, },
    { dsimp,
      rw ← nat_iso.naturality_2 (eq_to_iso (F.map_comp _ _)) f.fiber,
      simp,
      refl, },
  end, }

namespace grothendieck

/-- The forgetful functor from `grothendieck F` to the source category. -/
@[simps]
def forget : grothendieck F ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.1, }

end grothendieck
