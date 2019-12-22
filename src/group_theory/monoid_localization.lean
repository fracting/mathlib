/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import group_theory.congruence
import algebra.associated
import tactic.abel

/-!
# Localizations of commutative monoids

The standard congruence relation (an equivalence relation preserving a binary operation) used to
define commutative ring localizations does not rely on the ring's addition. For a commutative
monoid `X` and submonoid `Y`, this relation can be expressed as
`∀ (x₁, y₁) (x₂, y₂) : X × Y, x ∼ y ↔ ∃ c ∈ Y, c * x₁ * y₂ = c * x₂ * y₁`, or, equivalently, as the
unique congruence relation `r` on `X × Y` such that for any other congruence relation `r'` on
`X × Y` where for all `y ∈ Y`, `(1, 1) ∼ (y, y)` under `r'`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by
`r'` implies `(x₁, y₁) ∼ (x₂, y₂)` by `r`.

The first half of the file contains basic lemmas about the localization of `X` at `Y` - the
commutative monoid we get when we quotient `X × Y` by this congruence relation - and some
associated monoid homomorphisms: the quotient map, `monoid_localization.mk`, the quotient map
restricted to `X × {1}`, `monoid_localization.of`, and the quotient map restricted to `Y × {1}`,
`monoid_localization.to_units`, whose image is contained in the unit group of the localization of
`X` at `Y`.
Subsequently we prove basic lemmas about `monoid_localization.lift'` (constructive version) and
`monoid_localization.lift` (classical version): given a `comm_monoid` homomorphism `f : X → Z`
mapping elements of a submonoid `Y` to invertible elements of `Z`, these are the homomorphism
from the localization of `X` at `Y` sending `⟦(x, y)⟧` to `f(x) * f(y)⁻¹`. If `f(Y)` is contained
in a submonoid `W` of `Z`, we can also define the map from the localization of `X` at `Y`
to the localization of `Z` at `W` induced by `(of W) ∘ f`, where `of W` is the natural map from `Z`
to the localization of `Z` at `W`. This is called `monoid_localization.map`. We show that given an
isomorphism `h` between `X` and `Z` such that `h(Y) = W`, applying `map` to `h` gives an
isomorphism between `monoid_localization X Y` and `monoid_localization Z W`.

We next define a predicate, `char_pred`, characterizing `comm_monoid`s isomorphic to the
localization of `X` at `Y`. Proving statements about monoids satsifying the characteristic
predicate allows us to reason 'up to isomorphism', given that we cannot easily replace a structure
with an isomorphic structure of an unequal type.

This is followed by some lemmas about the localization of `X` at the submonoid generated by an
element `x : X`.

The last section of the file concerns the localization of `X` at the top element of the lattice
of submonoids of `X`: the whole of `X`. This construction, denoted `completion X`, is a commutative
group sometimes known as the Grothendieck group of `X`, and the map sending `X` to `completion X`
gives rise to a functor left adjoint to the forgetful functor from the category of commutative
groups to the category of commutative monoids. Its action on morphisms is defined by
`completion.map`.

## Implementation notes

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens many proofs.

The `private def` `r'.rel` and the lemmas `r'.add, r'.transitive` are to enable the use of the
`abel` tactic for both the additive and multiplicative proofs that the 'usual' localization
congruence relation is a congruence relation.

There is only a multiplicative version for any lemma or definition relying on a unit group of a
`comm_monoid`; additive versions would require additive unit groups.

We do not use the category theory library to define the adjunction (`hom_equiv` and
`hom_equiv_naturality_left_symm`) for the sake of clarity.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
group completion, Grothendieck group
-/

variables {X : Type*}

namespace submonoid

/-- The congruence relation on `X × Y`, `X` a `comm_monoid` and `Y` a submonoid of `X`, whose
    quotient is the localization of `X` at `Y`, defined as the unique congruence relation on
    `X × Y` such that for any other congruence relation `s` on `X × Y` where for all `y ∈ Y`,
    `(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s` implies
    `(x₁, y₁) ∼ (x₂, y₂)` by `r`. -/
@[to_additive "The congruence relation on `X × Y`, `X` an `add_comm_monoid` and `Y` an `add_submonoid` of `X`, whose quotient is the localization of `X` at `Y`, defined as the unique congruence relation on `X × Y` such that for any other congruence relation `s` on `X × Y` where for all `y ∈ Y`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s` implies `(x₁, y₁) ∼ (x₂, y₂)` by `r`."]
def r [comm_monoid X] (Y : submonoid X) : con (X × Y) :=
lattice.Inf {c | ∀ y : Y, c 1 (y, y)}

end submonoid

namespace add_submonoid

variables [add_comm_monoid X]

/-- An alternate form of the `add_monoid` localization relation, stated here for readability of the
    next few lemmas. -/
private def r'.rel (Y : add_submonoid X) (a b : X × Y) :=
∃ c : Y, (c : X) + (a.1 + b.2) = c + (b.1 + a.2)

lemma r'.transitive {Y : add_submonoid X} : transitive (r'.rel Y) :=
λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨n + m + b.2,
  calc
    ↑n + ↑m + ↑b.2 + (a.1 + ↑c.2)
      = ↑n + (↑m + (b.1 + ↑a.2)) + ↑c.2 : by rw ←hm; abel
  ... = ↑m + (↑n + (c.1 + ↑b.2)) + ↑a.2 : by rw ←hn; abel
  ... = ↑n + ↑m + ↑b.2 + (c.1 + ↑a.2) : by abel⟩

lemma r'.add {Y : add_submonoid X} {a b c d} :
  r'.rel Y a b → r'.rel Y c d → r'.rel Y (a + c) (b + d) :=
λ ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n,
  calc
    ↑m + ↑n + (a.1 + c.1 + (↑b.2 + ↑d.2))
      = ↑n + c.1 + (↑m + (b.1 + ↑a.2)) + ↑d.2 : by rw ←hm; abel
  ... = (↑m + (b.1 + ↑a.2)) + (↑n + (d.1 + ↑c.2)) : by rw ←hn; abel
  ... = ↑m + ↑n + (b.1 + d.1 + (↑a.2 + ↑c.2)) : by abel⟩

/-- An alternate form of the congruence relation on `X × Y`, `X` an `add_comm_monoid` and `Y` an
    `add_submonoid` of `X`, whose quotient is the localization of `X` at `Y`. Its equivalence to
    `r` can be useful for proofs. -/
def r' (Y : add_submonoid X) : add_con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c : X) + (a.1 + b.2) = c + (b.1 + a.2),
  iseqv := ⟨λ _, ⟨0, rfl⟩, λ _ _ ⟨c, hc⟩, ⟨c, hc.symm⟩, r'.transitive⟩,
  add' := λ a b c d, r'.add }

end add_submonoid

variables [comm_monoid X] (Y : submonoid X) {Z : Type*} [comm_monoid Z]

namespace submonoid

/-- An alternate form of the congruence relation on `X × Y`, `X` a `comm_monoid` and `Y` a
    submonoid of `X`, whose quotient is the localization of `X` at `Y`. Its equivalence to `r` can
    be useful for proofs. -/
def r' : con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c : X) * (a.1 * b.2) = c * (b.1 * a.2),
  iseqv := ⟨λ _, ⟨1, rfl⟩, λ _ _ ⟨c, hc⟩, ⟨c, hc.symm⟩,
    @add_submonoid.r'.transitive (additive X) _ $ submonoid.to_add_submonoid Y⟩,
  mul' := @add_submonoid.r'.add (additive X) _ $ submonoid.to_add_submonoid Y }

attribute [to_additive add_submonoid.r'] submonoid.r'

/-- The congruence relation used to localize a `comm_monoid` at a submonoid can be expressed
    equivalently as an infimum (see `submonoid.r`) or explicitly (see `submonoid.r'`). -/
@[to_additive "The additive congruence relation used to localize an `add_comm_monoid` at a submonoid can be expressed equivalently as an infimum (see `add_submonoid.r`) or explicitly (see `add_submonoid.r'`)."]
theorem r_eq_r' : Y.r = Y.r' :=
le_antisymm (lattice.Inf_le $ λ _, ⟨1, by simp⟩) $
  lattice.le_Inf $ λ b H x y ⟨t, ht⟩,
    begin
      rw [show x = (1 * x.1, 1 * x.2), by simp, show y = (1 * y.1, 1 * y.2), by simp],
      refine b.trans
       (show b _ ((t : X) * y.2 * x.1, t * y.2 * x.2), from
         b.mul (H (t * y.2)) $ b.refl (x.1, x.2)) _,
      rw [mul_assoc, mul_comm _ x.1, ht, mul_comm y.1, mul_assoc, mul_comm y.2,
          ←mul_assoc, ←mul_assoc],
      exact b.mul (b.symm $ H $ t * x.2) (b.refl (y.1, y.2))
    end

end submonoid

variables (X)

/-- The localization of a `comm_monoid` at one of its submonoids. -/
@[to_additive add_monoid_localization "The localization of an `add_comm_monoid` at one of its submonoids."]
def monoid_localization := Y.r.quotient

variables {X Y}

namespace monoid_localization

/-- For all `y` in `Y`, a submonoid of a `comm_monoid` `X`, `(1, 1) ∼ (y, y)` under the relation
    defining the localization of `X` at `Y`. -/
@[to_additive "For all `y` in `Y`, a submonoid of an `add_comm_monoid` `X`, `(0, 0) ∼ (y, y)` under the relation defining the localization of `X` at `Y`."]
lemma one_rel (y : Y) : Y.r 1 (y, y) := by rw Y.r_eq_r'; use 1; norm_num

/-- Given a `comm_monoid` `X` and submonoid `Y`, `mk` sends `x : X`, `y ∈ Y` to the equivalence
    class of `(x, y)` in the localization of `X` at `Y`. -/
@[to_additive "Given an `add_comm_monoid` `X` and submonoid `Y`, `mk` sends `x : X`, `y ∈ Y` to the equivalence class of `(x, y)` in the localization of `X` at `Y`."]
def mk (x : X) (y : Y) : monoid_localization X Y := Y.r.mk' (x, y)

@[elab_as_eliminator, to_additive]
theorem ind {p : monoid_localization X Y → Prop}
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) (x) : p x :=
by rcases x; convert H x; exact prod.mk.eta.symm

@[elab_as_eliminator, to_additive]
theorem induction_on {p : monoid_localization X Y → Prop} (x)
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) : p x := ind H x

@[to_additive] lemma exists_rep (x) : ∃ y : X × Y, mk y.1 y.2 = x :=
induction_on x $ λ y, ⟨y, rfl⟩

@[to_additive] instance : has_mul (monoid_localization X Y) := Y.r.has_mul

@[to_additive] instance : comm_monoid (monoid_localization X Y) :=
Y.r.comm_monoid

@[to_additive] protected lemma eq {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ Y.r (a₁, a₂) (b₁, b₂) :=
Y.r.eq.trans $ iff.rfl

@[to_additive] protected lemma eq' {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∃ c : Y, (c : X) * (a₁ * b₂) = c * (b₁ * a₂) :=
⟨λ h, let ⟨w, hw⟩ := show Y.r' (a₁, a₂) (b₁, b₂), by rw [←Y.r_eq_r', ←con.eq]; exact h in ⟨w, hw⟩,
 λ ⟨w, hw⟩, Y.r.eq.2 $ by rw [Y.r_eq_r']; exact ⟨w, hw⟩⟩

@[to_additive] lemma mk_eq_of_eq {a₁ b₁} {a₂ b₂ : Y} (h : (a₂ : X) * b₁ = b₂ * a₁) :
  mk a₁ a₂ = mk b₁ b₂ :=
monoid_localization.eq'.2 $ ⟨1, by rw [mul_comm b₁, h, mul_comm a₁]⟩

@[simp, to_additive] lemma mk_self' (x : Y) : mk (x : X) x = 1 :=
monoid_localization.eq.2 $ λ c h, c.symm $ h x

@[simp, to_additive] lemma mk_self {x} (hx : x ∈ Y) : mk x ⟨x, hx⟩ = 1 :=
mk_self' ⟨x, hx⟩

@[simp, to_additive] lemma mk_mul_mk (x y) (s t : Y) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

/-- Definition of the function on the localization of a `comm_monoid` at a submonoid induced by a
    function that is constant on the equivalence classes of the localization relation. -/
@[simp, to_additive "Definition of the function on the localization of an `add_comm_monoid` at an `add_submonoid` induced by a function that is constant on the equivalence classes of the localization relation."]
lemma lift_on_beta {β} (f : (X × Y) → β) (H : ∀ a b, Y.r a b → f a = f b) (x y) :
con.lift_on (mk x y) f H = f (x, y) := rfl

/-- Natural homomorphism sending `x : X`, `X` a `comm_monoid`, to the equivalence class of
    `(x, 1)` in the localization of `X` at a submonoid. For a `comm_ring` localization, this is
    a ring homomorphism named `localization.of`. -/
@[to_additive "Natural homomorphism sending `x : X`, `X` an `add_comm_monoid`, to the equivalence class of `(x, 0)` in the localization of `X` at a submonoid."]
def of (Y) : X →* monoid_localization X Y :=
Y.r.mk'.comp ⟨λ x, (x, 1), refl 1, λ _ _, by simp only [prod.mk_mul_mk, one_mul]⟩

@[to_additive] lemma of_ker_iff {x y} : con.ker (of Y) x y ↔ Y.r (x, 1) (y, 1) :=
con.eq _

@[to_additive] lemma of_eq_mk (x) : of Y x = mk x 1 := rfl

@[simp, to_additive] lemma of_mul_mk (x y v) : of Y x * mk y v = mk (x * y) v :=
by rw [of_eq_mk, mk_mul_mk, one_mul]

@[simp, to_additive] lemma mk_mul_of (x y v) : mk y v * of Y x = mk (x * y) v :=
by rw [mul_comm, of_mul_mk]

@[to_additive] lemma mk_eq_mul_mk_one (x y) : mk x y = of Y x * mk 1 y :=
by rw [of_mul_mk, mul_one]

@[simp, to_additive] lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk (x * y) y = of Y x :=
by rw [mk_eq_mul_mk_one, (of Y).map_mul, mul_assoc, ←mk_eq_mul_mk_one, mk_self', mul_one]

@[simp, to_additive] lemma mk_mul_cancel_left (x : X) (y : Y) :
  mk ((y : X) * x) y = of Y x :=
by rw [mul_comm, mk_mul_cancel_right]

/-- Natural homomorphism sending `y ∈ Y`, `Y` a submonoid of a `comm_monoid` `X`, to the units of
    the localization of `X` at `Y`. -/
def to_units (Y : submonoid X) : Y →* units (monoid_localization X Y) :=
⟨λ y, ⟨mk y 1, mk 1 y, by simp, by simp⟩, by simp; refl,
 λ _ _, by ext; convert (of Y).map_mul _ _⟩

@[simp] lemma to_units_mk (y) : (to_units Y y : monoid_localization X Y) = mk y 1 := rfl

@[simp] lemma mk_is_unit (y : Y) : is_unit (mk (y : X) (1 : Y)) :=
is_unit_unit $ to_units Y y

@[simp] lemma mk_is_unit' (x) (hx : x ∈ Y) : is_unit (mk x (1 : Y)) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_inv (y) : mk 1 y = ↑(to_units Y y)⁻¹ := rfl

@[simp] lemma of_is_unit (y : Y) : is_unit (of Y y) :=
is_unit_unit $ to_units Y y

@[simp] lemma of_is_unit' (x) (hx : x ∈ Y) : is_unit (of Y x) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_map_inv (g : monoid_localization X Y →* Z) (y) :
  g ↑(to_units Y y)⁻¹ = ↑(units.map g (to_units Y y))⁻¹ :=
by rw [←units.coe_map, (units.map g).map_inv]

lemma mk_eq (x y) : mk x y = of Y x * ↑(to_units Y y)⁻¹ :=
by rw ←to_units_inv; simp only [of_eq_mk, mk_mul_mk, mul_one, one_mul]

lemma map_units_of_comp_of {h : monoid_localization X Y →* Z} (y : Y) :
  is_unit (h.comp (of Y) y) :=
⟨units.map h (to_units Y y), rfl⟩

variables {f : X →* Z}

lemma is_unit_of_of_comp {W : submonoid Z} (hf : ∀ y : Y, f y ∈ W) {y : Y} :
  is_unit (of W (f y)) :=
⟨to_units W ⟨f y, hf y⟩, rfl⟩

variables {g : Y → units Z}

lemma units_restrict_mul (H : ∀ y : Y, f y = g y) {x y} : g (x * y) = g x * g y :=
by ext; rw [units.coe_mul, ←H _, ←H _, ←H _]; apply f.map_mul

variables (f)

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the induced homomorphism from `Y` to the units of `Z`. -/
def units_restrict (H : ∀ y : Y, f y = g y) : Y →* units Z :=
⟨g, units.ext $ (H 1) ▸ f.map_one, λ _ _, units_restrict_mul H⟩

variables (g)

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from `X × Y` to `Z` sending `(x, y)` to
    `f(x) * f(y)⁻¹`; this induces a homomorphism from the localization of `X` at `Y`
    (constructive version). -/
def aux (H : ∀ y : Y, f y = g y) : X × Y →* Z :=
(f.comp prod.monoid_hom.fst).mul $
  (units.coe_hom Z).comp ((units_restrict f H).comp prod.monoid_hom.snd).inv

variables {g}

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from `X × Y` to `Z` sending `(x, y)` to
    `f(x) * f(y)⁻¹` is constant on the equivalence classes of the localization of `X` at `Y`. -/
lemma r_le_ker_aux (H : ∀ y : Y, f y = g y) :
  Y.r ≤ con.ker (aux f g H) :=
con.Inf_le _ _ (λ y, show f (1 : Y) * ↑(g 1)⁻¹ = f y * ↑(g y)⁻¹, by
  rw [H 1, H y]; simp [units.mul_inv])

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from the localization of `X` at `Y` sending
    `⟦(x, y)⟧` to `f(x) * f(y)⁻¹`. -/
def lift' (g : Y → units Z) (H : ∀ y : Y, f y = g y) : monoid_localization X Y →* Z :=
Y.r.lift (aux f g H) $ r_le_ker_aux f H

/-- Given a `comm_monoid` homomorphism `f : X → Z` mapping elements of a submonoid `Y` to
    invertible elements of `Z`, the homomorphism from the localization of `X` at `Y` sending
    `⟦(x, y)⟧` to `f(x) * f(y)⁻¹`, where `f(y)⁻¹` is chosen nonconstructively. -/
noncomputable def lift (H : ∀ y : Y, is_unit (f y)) : monoid_localization X Y →* Z :=
lift' f _ $ λ _, classical.some_spec $ H _

variables {f}

@[simp] lemma lift'_mk (H : ∀ y : Y, f y = g y) (x y) :
  lift' f _ H (mk x y) = f x * ↑(g y)⁻¹ := rfl

@[simp] lemma lift_mk (H : ∀ y : Y, is_unit (f y)) (x y) :
  lift f H (mk x y) = f x * ↑(classical.some (H y))⁻¹ := rfl

@[simp] lemma lift'_of (H : ∀ y : Y, f y = g y) (x : X) :
  lift' f _ H (of Y x) = f x :=
show f x * ↑(g 1)⁻¹ = _, by
  rw [inv_eq_one.2 (show g 1 = 1, from units.ext $ (H 1) ▸ f.map_one), units.coe_one, mul_one]

@[simp] lemma lift_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H (of Y x) = f x := lift'_of _ _

lemma lift'_eq_iff (H : ∀ y : Y, f y = g y) {x y : X × Y} :
  lift' f g H (mk x.1 x.2) = lift' f g H (mk y.1 y.2) ↔ f (y.2 * x.1) = f (y.1 * x.2) :=
by rw [lift'_mk, lift'_mk, units.eq_mul_inv_iff_mul_eq, mul_comm, ←mul_assoc,
       units.mul_inv_eq_iff_eq_mul, ←H _, ←H _, ←f.map_mul, ←f.map_mul]

lemma lift_eq_iff (H : ∀ y : Y, is_unit (f y)) {x y : X × Y} :
  lift f H (mk x.1 x.2) = lift f H (mk y.1 y.2) ↔ f (y.2 * x.1) = f (y.1 * x.2) :=
lift'_eq_iff _

lemma mk_eq_iff_of_eq {x y : X × Y} :
  mk x.1 x.2 = mk y.1 y.2 ↔ of Y (y.2 * x.1) = of Y (y.1 * x.2) :=
by rw [mk_eq, mk_eq, ←lift'_mk, ←lift'_mk];
  exact lift'_eq_iff (λ (w : Y), rfl)

lemma lift'_comp_of (H : ∀ y : Y, f y = g y) :
  (lift' f _ H).comp (of Y) = f :=
by ext; exact lift'_of H _

@[simp] lemma lift_comp_of (H : ∀ y : Y, is_unit (f y)) :
  (lift f H).comp (of Y) = f := lift'_comp_of _

@[simp] lemma lift'_apply_of (f' : monoid_localization X Y →* Z)
  (H : ∀ y : Y, f'.comp (of Y) y = g y) : lift' (f'.comp (of Y)) _ H = f' :=
begin
  ext x,
  apply induction_on x,
  intros,
  rw [lift'_mk, units.mul_inv_eq_iff_eq_mul, ←H y.2, mk_eq_mul_mk_one],
  show f' _ = f' (mk _ _ * _) * f' (mk _ _),
  rw [←f'.map_mul, mk_mul_mk, mk_mul_mk],
  simp only [mul_one, mk_mul_cancel_right, one_mul],
end

@[simp] lemma lift_apply_of (g : monoid_localization X Y →* Z) :
  lift (g.comp $ of Y) (λ y, is_unit_unit $ units.map g $ to_units Y y) = g :=
lift'_apply_of _ _

lemma  funext (f g : monoid_localization X Y →* Z)
  (h : ∀ a, f.comp (of Y) a = g.comp (of Y) a) : f = g :=
begin
  rw [←lift_apply_of f, ←lift_apply_of g],
  congr' 1,
  ext,
  convert h x,
end

lemma lift_surjective_iff (H : ∀ y : Y, is_unit (f y)) :
  (∀ z : Z, ∃ x : X × Y, f x.1 = z * f x.2) ↔ function.surjective (lift f H) :=
⟨λ h z, let ⟨x, hx⟩ := h z in ⟨monoid_localization.mk x.1 x.2, by
  rw [lift_mk, hx, units.mul_inv_eq_iff_eq_mul];
  exact congr_arg ((*) z) (classical.some_spec $ H x.2)⟩,
 λ h z, let ⟨x, hx⟩ := h z in
  begin
    revert hx,
    apply monoid_localization.induction_on x,
    intros y hy,
    use y,
    rw [lift_mk, units.mul_inv_eq_iff_eq_mul] at hy, rw hy,
    exact congr_arg ((*) z) (classical.some_spec $ H y.2).symm
  end⟩

variables {W : submonoid Z} (f)

/-- Given a `comm_monoid` homomorphism `f : X → Z` where for submonoids `Y ⊆ X, W ⊆ Z` we have
    `f(Y) ⊆ W`, the monoid homomorphism from the localization of `X` at `Y` to the localization of
    `Z` at `W` induced by the natural map from `Z` to the localization of `Z` at
    `W` composed with `f`. -/
def map (hf : ∀ y : Y, f y ∈ W) : monoid_localization X Y →* monoid_localization Z W :=
lift' ((of W).comp f) ((to_units W).comp $ (f.comp Y.subtype).subtype_mk W hf) $ λ y, rfl

variables {f}

lemma map_eq (hf : ∀ y : Y, f y ∈ W) :
  map f hf = lift ((of W).comp f) (λ y, ⟨to_units W ⟨f y, hf y⟩, rfl⟩) :=
begin
  rw map,
  congr,
  ext,
  erw ←classical.some_spec (is_unit_of_of_comp hf),
  refl
end

@[simp] lemma map_of (hf : ∀ y : Y, f y ∈ W) (x) :
  map f hf (of Y x) = of W (f x) := lift'_of _ _

@[simp] lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  (map f hf).comp (of Y) = (of W).comp f := lift'_comp_of _

lemma map_mk (hf : ∀ y : Y, f y ∈ W) (x y) :
  map f hf (mk x y) = mk (f x) ⟨f y, hf y⟩ :=
(lift'_mk _ _ _).trans (mk_eq _ _).symm

@[simp] lemma map_id (x : monoid_localization X Y) :
  map (monoid_hom.id X) (λ (y : Y), y.2) x = x :=
induction_on x $ λ ⟨w, z⟩, by rw map_mk; exact congr_arg _ (subtype.eq' rfl)

lemma map_comp_map {A} [comm_monoid A] {V} {g : Z →* A}
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, hf y⟩) :=
funext _ _ $ λ x, by simp only [map_of, monoid_hom.comp_apply]

lemma map_map {A} [comm_monoid A] {V} {g : Z →* A}
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) (x) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg ⟨f y, hf y⟩) x :=
by rw ←map_comp_map hf hg; refl

@[ext] lemma map_ext (g : X →* Z) (hf : ∀ y : Y, f y ∈ W) (hg : ∀ y : Y, g y ∈ W)
  (h : f = g) (x) : map f hf x = map g hg x :=
induction_on x $ λ _,
begin
  rw [map_mk, map_mk],
  congr;
  rw h;
  refl
end

open mul_equiv function

/-- Given `comm_monoid`s `X, Z`, submonoids `Y ⊆ X, W ⊆ Z` and an isomorphism `h` of `X, Z` such
    that `h(Y) = Z,` the isomorphism between `monoid_localization X Y` and
    `monoid_localization Z W` induced by the map sending `x : X` to the equivalence class of
    `(h x, 1)` in `monoid_localization Z W`. -/
def mul_equiv_map (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  monoid_localization X Y ≃* monoid_localization Z W :=
by refine { to_fun := map h.to_monoid_hom $ λ y : Y, show h y ∈ W, from
    H ▸ set.mem_image_of_mem h y.2,
  inv_fun := map h.symm.to_monoid_hom $ λ (w : W),
    begin
      obtain ⟨y, hym, hy⟩ : (w : Z) ∈ h.to_monoid_hom.map Y := H.symm ▸ w.2,
      show h.symm w ∈ Y,
      erw [hy.symm, symm_apply_apply],
      exact hym,
    end,
  map_mul' := (map _ _).map_mul, ..};
begin
  intro x,
  rw map_map,
  conv_rhs {rw ←map_id x},
  ext y,
  simpa,
end

variables (f)

/-- Given a `comm_monoid` `X` and a submonoid `Y ⊆ X`, the predicate characterizing `comm_monoid`s
    isomorphic to the localization of `X` at `Y`. These are precisely the images of the
    homomorphisms from the localization of `X` at `Y` induced by `comm_monoid` homomorphisms `f`
    such that `f(Y)` consists of invertible elements, and for all `x, y : X`, `f(x) = f(y)` iff
    `∃ c ∈ Y, c * x = c * y`. -/
def char_pred (H : ∀ y : Y, is_unit (f y)) :=
(∀ z : Z, ∃ x : X × Y, f x.1 = z * f x.2) ∧ ∀ x y, f x = f y ↔ of Y x = of Y y

variables {f}

lemma lift_inj_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
  injective (lift f H) :=
λ x y, induction_on x $ λ w, induction_on y $ λ z hf,
  mk_eq_iff_of_eq.2 $ (Hp.2 _ _).1 $ (lift'_eq_iff _).1 hf

variables (f)

/-- Given `comm_monoid`s `X, Z`, a submonoid `Y ⊆ X`, and a homomorphism `f : X → Z` satsifying
    the predicate characterizing monoids isomorphic to `monoid_localization X Y`, the homomorphism
    from `monoid_localization X Y` to `Z` induced by `f` is an isomorphism. -/
noncomputable def mul_equiv_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
  monoid_localization X Y ≃* Z :=
{ to_fun := lift f H,
  inv_fun := λ y, classical.some $ (lift_surjective_iff H).1 Hp.1 y,
  left_inv := right_inverse_of_injective_of_left_inverse
    (lift_inj_of_char_pred H Hp) $ λ y, classical.some_spec $ (lift_surjective_iff H).1 Hp.1 y,
  right_inv := λ y, classical.some_spec $ (lift_surjective_iff H).1 Hp.1 y,
  map_mul' := (lift f H).map_mul }

/-- Given `comm_monoid`s `X, Z`, a submonoid `Y ⊆ X` and an isomorphism `h` between the
    localization of `X` at `Y` and `Z`, the map sending `x : X` to `h(⟦(x, 1)⟧)` satisfies the
    localization characteristic predicate. -/
lemma char_pred_of_mul_equiv (h : monoid_localization X Y ≃* Z) :
  char_pred (h.to_monoid_hom.comp $ of Y) map_units_of_comp_of :=
⟨(lift_surjective_iff map_units_of_comp_of).2 $ λ x,
   let ⟨p, hp⟩ := h.to_equiv.surjective x in ⟨p, by erw [←hp, lift_apply_of]; refl⟩,
 λ _ _, show h _ = h _ ↔ _, from ⟨λ H, h.to_equiv.injective H, congr_arg h⟩⟩

/-- Given `comm_monoid`s `X, Z`, a submonoid `Y ⊆ X` and a homomorphism `f : X → Z`, if
    `f(Y) ⊆ units Z` and `f` induces an isomorphism between the localization of `X` at `Y` and `Z`,
    then `f` satisfies the localization characteristic predicate. -/
lemma char_pred_of_equiv (H : ∀ y : Y, is_unit (f y)) (h : monoid_localization X Y ≃ Z)
  (hf : (h : monoid_localization X Y → Z) = lift f H) : char_pred f H :=
⟨(lift_surjective_iff H).2 $ λ x, let ⟨p, hp⟩ := h.surjective x in ⟨p, by rw [←hp, ←hf]; refl⟩,
 λ x y, (of_ker_iff.trans $ by
   rw ←con.ker_eq_lift_of_injective Y.r
     (aux f (λ _, classical.some $ H _) $ λ _, classical.some_spec $ H _)
     (r_le_ker_aux _ $ λ _, classical.some_spec $ H _)
     (λ _ _ hi, h.injective $ by erw hf; exact hi);
   exact units.mul_right_inj _).symm⟩

/-- The localization of a `comm_monoid` `X` at a submonoid `Y ⊆ X` satisfies the predicate
    characterizing `comm_monoid`s isomorphic to the localization of `X` at `Y`. -/
lemma char_pred_of_localization : char_pred (of Y) (λ y, ⟨to_units Y y, rfl⟩) :=
let H : ∀ y : Y, is_unit (of Y y) := λ y, ⟨to_units Y y, rfl⟩ in
⟨λ y, monoid_localization.induction_on y $ λ x,
  ⟨x, by rw [mk_mul_of, mk_mul_cancel_left]⟩, by tauto⟩

/-- The localization of a `comm_monoid` `X` at the submonoid generated by an element `x : X`. -/
@[reducible] def away (x) := monoid_localization X $ submonoid.powers x

section away

  /-- Given a `comm_monoid` `X` and `x : X`, the inverse of `⟦(x, 1)⟧` in the localization of `X`
      at the submonoid generated by `x`. -/
  def away.inv_self (x : X) : away x := mk 1 ⟨x, 1, pow_one x⟩

  variables (f)

  /-- Given a `comm_monoid` `X`, an element `x : X` and a `comm_monoid` homomorphism `f : X → Z`
      mapping `x` to an invertible element of `Z`, the homomorphism induced from the localization
      of `X` at the submonoid generated by `x` to `Z`. -/
  @[elab_with_expected_type]
  noncomputable def away.lift {x} (hfx : is_unit (f x)) : away x →* Z :=
  lift' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
  by rw [units.coe_pow, ←classical.some_spec hfx,
         ←f.map_pow, classical.some_spec s.2]; refl

  @[simp] lemma away.lift_of {x} (hfx : is_unit (f x)) (a) :
    away.lift f hfx (of (submonoid.powers x) a) = f a :=
  lift'_of _ _

  @[simp] lemma away.lift_comp_of {x} (hfx : is_unit (f x)) :
    (away.lift f hfx).comp (of $ submonoid.powers x) = f :=
  lift'_comp_of _

  /-- Given a `comm_monoid` `X` and elements `x y : X`, the homomorphism from the localization of
      `X` at the submonoid generated by `x` to the localization of `X` at the submonoid generated
      by `x * y` induced by the map sending `a : X` to the equivalence class of (a, 1) in
      `away (x * y)`. -/
  noncomputable def away_to_away_right (x y : X) : away x →* away (x * y) :=
  away.lift (of $ submonoid.powers (x * y)) $
  is_unit_of_mul_one _
    (((of $ submonoid.powers (x * y)) : X → away (x * y)) y * away.inv_self (x * y)) $ by
      rw [away.inv_self, ←mul_assoc, ←(of _).map_mul, ←mk_self (show _ ∈ submonoid.powers (x * y),
            from ⟨1, pow_one _⟩), mk_eq_mul_mk_one (x * y) _]

end away

end monoid_localization

namespace add_monoid_localization

variables {A : Type*} [add_comm_monoid A] (x : A)

/-- The localization of an `add_comm_monoid` `A` at the submonoid generated by an element
    `x : A`. -/
@[reducible] def away := add_monoid_localization A (add_submonoid.multiples x)

attribute [to_additive add_monoid_localization.away] monoid_localization.away

/-- Given an `add_comm_monoid` `A` and `x : A`, the inverse of `⟦(x, 0)⟧` in the localization of
    `A` at the `add_submonoid` generated by `x`. -/
def away.neg_self : away x := mk 0 ⟨x, 1, add_monoid.one_smul x⟩

attribute [to_additive add_monoid_localization.away.neg_self] monoid_localization.away.inv_self

end add_monoid_localization

namespace comm_monoid
variables (X)

/-- The Grothendieck group of a `comm_monoid` `X`: the localization of `X` at itself. -/
@[reducible, to_additive "The Grothendieck group of an `add_comm_monoid` `X`: the localization of `X` at itself."]
abbreviation completion := monoid_localization X (⊤ : submonoid X)

namespace completion
open monoid_localization
variables {X}

/-- The quotient map sending elements `x, y` of a `comm_monoid` `X` to the equivalence
    class of `(x, y)` in the localization of `X` at itself. -/
@[to_additive "The quotient map sending elements `x, y` of an `add_comm_monoid` `X` to the equivalence class of `(x, y)` in the localization of `X` at itself."]
protected def mk (x y) : completion X :=
  monoid_localization.mk x (⟨y, trivial⟩ : (⊤ : submonoid X))

/-- Given a `comm_monoid` `X`, the congruence relation defining the Grothendieck group of `X`:
    the localization of `X` at itself. -/
@[to_additive "Given an `add_comm_monoid` `X`, the additive congruence relation defining the Grothendieck group of `X`: the localization of `X` at itself."]
protected def r (x y : X × X) := (⊤ : submonoid X).r (x.1, ⟨x.2, trivial⟩) (y.1, ⟨y.2, trivial⟩)

/-- The function on the quotient by a congruence relation `c` induced by a function that is
    constant on `c`'s equivalence classes. -/
@[elab_as_eliminator, to_additive "The function on the quotient by a congruence relation `c` induced by a function that is constant on `c`'s equivalence classes."]
protected def lift_on (q : completion X) (f : X × X → Z)
  (h : ∀ a b, completion.r a b → f a = f b) : Z := con.lift_on q
  (λ x, f (x.1, x.2)) $ λ a b H, h (a.1, a.2) (b.1, b.2) $ by
    unfold completion.r; simpa using H

variables (X)

/-- The natural map sending an element `x` of a `comm_monoid` `X` to the equivalence
    class of `(x, 1)` in the localization of `X` at itself. -/
@[to_additive "The natural map sending an element `x` of an `add_comm_monoid` `X` to the equivalence class of `(x, 0)` in the localization of `X` at itself."]
protected def of : X →* completion X :=
⟨λ x, completion.mk x 1, rfl, λ x y,
  show _ = completion.mk (x * y) (1 * 1), by rw mul_one⟩

variables {X}

@[to_additive] instance : has_inv (completion X) :=
⟨λ y, completion.lift_on y (λ x, completion.mk x.2 x.1) $ λ a b h,
let ⟨c, hc⟩ := monoid_localization.eq'.1 $ (con.eq _).2 h in
  monoid_localization.eq'.2 ⟨c, by rw [mul_comm a.2, mul_comm b.2]; simpa using hc.symm⟩⟩

@[simp, to_additive] lemma inv_apply (x :  X × X) :
(completion.mk x.1 x.2)⁻¹ = completion.mk x.2 x.1 := rfl

@[simp, to_additive] protected lemma mul_left_inv (x : completion X) : x⁻¹ * x = 1 :=
begin
  apply con.induction_on x,
  intro y,
  show completion.mk ((y.2 : X) * y.1) (y.1 * y.2) = 1,
  rw mul_comm,
  exact mk_self _,
end

@[to_additive] instance : comm_group (completion X) :=
{  inv := has_inv.inv,
   mul_left_inv := completion.mul_left_inv,
   ..con.comm_monoid _ }

/-- The localization of a `comm_group` `G` at itself is (isomorphic to) `G`. -/
def mul_equiv_of_group (G : Type*) [comm_group G] :
  G ≃* completion G :=
{ to_fun := completion.of G,
  inv_fun := monoid_localization.lift' (monoid_hom.id G) (λ (g : (⊤ : submonoid G)),
    _root_.to_units G (g : G)) $ λ g, rfl,
  left_inv := λ x, by erw lift'_of; refl,
  right_inv := λ x, monoid_localization.induction_on x $ λ y, by
    show completion.of G (y.1 * (y.2 : G)⁻¹) = _;
    erw [←mk_mul_cancel_right _ y.2, inv_mul_cancel_right],
  map_mul' := monoid_hom.map_mul _ }

/-- Given `comm_monoid`s `X, Z`, a homomorphism `f : X → Z` induces a homomorphism from the
    Grothendieck group of `X` to the Grothendieck group of `Z` sending `⟦(x, y)⟧` to
    `⟦(f x, f y)⟧`. -/
@[to_additive "Given `add_comm_monoid`s `X, Z`, a homomorphism `f : X → Z` induces a homomorphism from the Grothendieck group of `X` to the Grothendieck group of `Z` sending `⟦(x, y)⟧` to `⟦(f x, f y)⟧`."]
protected def map (f : X →* Z) : completion X →* completion Z :=
{ to_fun := λ y, completion.lift_on y (λ x, completion.mk (f x.1) (f x.2)) $ λ x y h,
    let ⟨c, hc⟩ := monoid_localization.eq'.1 $ monoid_localization.eq.2 h in
    monoid_localization.eq'.2 ⟨⟨f c, trivial⟩, by erw [←f.map_mul, ←f.map_mul, hc];
      simp only [f.map_mul, subtype.coe_mk]⟩,
  map_one' := mk_self _,
  map_mul' := λ x y, con.induction_on₂ x y $ λ _ _,
    show completion.mk _ _ = completion.mk _ _ * completion.mk _ _, by
      erw [f.map_mul, f.map_mul]; refl }

@[to_additive] lemma map_id : completion.map (monoid_hom.id X) = monoid_hom.id (completion X) :=
monoid_hom.ext $ λ y, monoid_localization.induction_on y $ λ x,
  show monoid_localization.mk x.1 _ = _, by erw subtype.coe_eta; refl

variables {A : Type*} [comm_monoid A]

@[to_additive] lemma map_comp (f : X →* Z) (g : Z →* A) :
  completion.map (g.comp f) = (completion.map g).comp (completion.map f) :=
monoid_hom.ext $ λ y, monoid_localization.induction_on y $ λ _, rfl

variables (X) (G : Type*) [comm_group G]

/-- `Hom(F(X), Y) ≃* Hom(X, G(Y))`, where `X` is a `comm_monoid`, `Y` is a `comm_group`, `G` is the
    forgetful functor and `F` is the functor sending `comm_monoid`s to their Grothendieck group,
    and whose action on morphisms is defined by `completion.map`. Given `f ∈ Hom(X, Y),` we get a
    homomorphism sending `⟦(x, y)⟧ ∈ completion X` to `f x * (f y)⁻¹ ∈ Y`.  -/
@[to_additive "`Hom(F(X), Y) ≃+ Hom(X, G(Y))`, where `X` is an `add_comm_monoid`, `Y` is an `add_comm_group`, `G` is the forgetful functor and `F` is the functor sending `add_comm_monoid`s to their Grothendieck group, and whose action on morphisms is defined by `completion.map`. Given `f ∈ Hom(X, Y),` we get a homomorphism sending `⟦(x, y)⟧ ∈ completion X` to `f x - f y ∈ Y`."]
def hom_equiv : (X →* G) ≃* (completion X →* G) :=
{ to_fun := λ f, con.lift (submonoid.r (⊤ : submonoid X))
    (⟨λ x, f x.1 * (f x.2)⁻¹, by simp, λ x y, by simp only [mul_inv_rev, prod.snd_mul,
      prod.fst_mul, f.map_mul, submonoid.coe_mul]; ac_refl⟩)
     $ λ a b h,
       begin
         rw [con.to_setoid_eq, ←@prod.mk.eta _ _ a, ←@prod.mk.eta _ _ b] at h,
         obtain ⟨c, hc⟩ := monoid_localization.eq'.1 (monoid_localization.eq.2 h),
         show f a.1 * (f a.2)⁻¹ = f b.1 * (f b.2)⁻¹,
         rw [eq_mul_inv_iff_mul_eq, mul_comm, ←mul_assoc, mul_comm (f b.2), ←f.map_mul,
             ←mul_left_inj (f c), ←mul_assoc, ←f.map_mul, hc, mul_inv_eq_iff_eq_mul, mul_assoc,
             f.map_mul, f.map_mul],
         refl,
       end,
  inv_fun := λ f, f.comp $ completion.of X,
  left_inv := λ f, monoid_hom.ext $ λ x,
    show f x * (f 1)⁻¹ = f x, by rw [f.map_one, one_inv, mul_one],
  right_inv := λ f, monoid_hom.ext $ λ y, monoid_localization.induction_on y $ λ x,
    begin
      dsimp,
      show f (completion.mk x.1 1) * (f (monoid_localization.mk x.2 1))⁻¹ = _,
      rw [mul_inv_eq_iff_eq_mul, ←f.map_mul, mk_mul_mk, mul_one, mk_mul_cancel_right],
      refl,
    end,
  map_mul' := λ f g, monoid_hom.ext $ λ y, monoid_localization.induction_on y $ λ x,
    show f x.1 * g x.1 * (f x.2 * g x.2)⁻¹ = f x.1 * (f x.2)⁻¹ * (g x.1 * (g x.2)⁻¹),
      by rw mul_inv; ac_refl }

variables {X G}

@[to_additive] lemma hom_equiv_naturality_left_symm (f : X →* Z) (g : Z →* G) :
 (hom_equiv X G) (g.comp f) = ((hom_equiv Z G) g).comp (completion.map f) :=
monoid_hom.ext $ λ x, monoid_localization.induction_on x $ λ _, rfl

lemma hom_equiv_unique (f : X →* G) (g : completion X →* G)
  (H : ∀ x, f x = g (completion.of X x)) : g = hom_equiv X G f :=
monoid_hom.ext $ λ y, monoid_localization.induction_on y $ λ x,
  begin
    erw [mk_eq, g.map_mul, ←H],
    rw [to_units_map_inv, units.mul_inv_eq_iff_eq_mul],
    show _ = (f (x.1 * 1)) * (f (1 * x.2))⁻¹ * g (completion.of X x.2),
    rw ←H,
    simp
  end

end completion
end comm_monoid