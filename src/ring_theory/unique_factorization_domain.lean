/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

Theory of unique factorization domains.

@TODO: setup the complete lattice structure on `factor_set`.
-/
import algebra.gcd_monoid
import ring_theory.integral_domain
import ring_theory.noetherian

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated

section prio
set_option default_priority 100 -- see Note [default priority]
/-- `comm_cancel_monoid_with_zero`s whose divisibility relation -/
class DCC_dvd (α : Type*) [comm_cancel_monoid_with_zero α] : Prop :=
(well_founded_dvd_not_unit : well_founded (λ a b : α, a ≠ 0 ∧ ∃ x, ¬is_unit x ∧ b = a * x))

export DCC_dvd (well_founded_dvd_not_unit)

instance is_noetherian_ring.DCC_dvd [integral_domain α] [is_noetherian_ring α] :
  DCC_dvd α :=
⟨by simp only [ideal.span_singleton_lt_span_singleton.symm];
   exact inv_image.wf (λ a, ideal.span ({a} : set α)) (well_founded_submodule_gt _ _)⟩

instance polynomial.DCC_dvd [integral_domain α] [DCC_dvd α] : DCC_dvd (polynomial α) :=
{ well_founded_dvd_not_unit := begin
    classical,
    apply rel_hom.well_founded, swap,
    exact (prod.lex_wf (with_top.well_founded_lt $ with_bot.well_founded_lt nat.lt_wf)
      _inst_2.well_founded_dvd_not_unit),
    exact {
      to_fun := λ p, (if p = 0 then ⊤ else ↑p.degree, p.leading_coeff),
      map_rel' := λ a b ⟨ane0, ⟨c, ⟨not_unit_c, bac⟩⟩⟩, begin
        rw bac, rw polynomial.degree_mul, rw if_neg ane0, by_cases c = 0,
        { simp only [h, if_true, polynomial.leading_coeff_zero, eq_self_iff_true, ne.def, mul_zero],
          apply prod.lex.left _ _ (lt_of_le_of_ne le_top _), apply with_top.coe_ne_top, },
        { simp only [h, ane0, if_false, ne.def, polynomial.leading_coeff_mul, or_self, mul_eq_zero],
          rename h cne0, by_cases c.degree = 0,
        { simp only [h, add_zero, ne.def, polynomial.leading_coeff_mul],
          apply prod.lex.right, split, {rw polynomial.leading_coeff_eq_zero, apply ane0},
          use c.leading_coeff, split, swap, {refl},
          contrapose! not_unit_c, rw polynomial.is_unit_iff, use c.leading_coeff,
          split, {exact not_unit_c}, rw polynomial.leading_coeff,
          convert (polynomial.eq_C_of_degree_eq_zero h).symm,
          apply polynomial.nat_degree_eq_of_degree_eq_some h,},
        { apply prod.lex.left, rw polynomial.degree_eq_nat_degree cne0 at *,
          rw [with_top.coe_lt_coe, polynomial.degree_eq_nat_degree ane0,
            ← with_bot.coe_add, with_bot.coe_lt_coe],
          apply lt_add_of_pos_right, apply nat.pos_of_ne_zero, contrapose! h, rw h, refl, }, }
      end }
  end }
end prio

namespace DCC_dvd

variables [comm_cancel_monoid_with_zero α]
open associates nat

@[priority 100]
instance of_DCC_dvd_associates [comm_cancel_monoid_with_zero α]
  [DCC_dvd (associates α)]: DCC_dvd α :=
⟨by { refine rel_hom.well_founded (rel_hom.mk associates.mk _) DCC_dvd.well_founded_dvd_not_unit,
  rintros a b ⟨ane0, ⟨c, ⟨hc, bac⟩⟩⟩,
  rw bac, split, { contrapose! ane0, exact mk_eq_zero.1 ane0, },
  use (associates.mk c), split, { rw is_unit_mk, exact hc, },rw mk_mul_mk, }⟩

variables [DCC_dvd α]

@[priority 100]
instance DCC_dvd_associates : DCC_dvd (associates α) :=
⟨begin
  have h : ∀ a : associates α, ∃ b : α, a = associates.mk b,
  { rw forall_associated, intro a, use a, },
  let f : associates α → α := λ a, classical.some (h a),
  have hf : ∀ a, associates.mk (f a) = a := λ a, (classical.some_spec (h a)).symm,
  refine rel_hom.well_founded { to_fun := f, map_rel' := _ } DCC_dvd.well_founded_dvd_not_unit,
  rintros a b ⟨h1, ⟨x, ⟨hnu, hx⟩⟩⟩,
  split, { contrapose! h1, rw [← hf a, h1], refl, },
  rw [← hf a, ← hf b, ← hf x, mk_mul_mk, mk_eq_mk_iff_associated] at hx,
  rcases hx with ⟨u, hu⟩, use (f x * ↑u⁻¹), split,
  { rw [← is_unit_mk, ← mk_mul_mk, hf x], contrapose! hnu, apply is_unit_of_mul_is_unit_left hnu, },
  rw [← mul_assoc, ← hu, mul_assoc], simp,
end⟩

theorem well_founded_associates : well_founded ((<) : associates α → associates α → Prop) :=
begin
  have h : ∀ a : associates α, ∃ b : α, a = associates.mk b,
  { rw forall_associated, intro a, use a, },
  let f : associates α → α := λ a, classical.some (h a),
  have hf : ∀ a, associates.mk (f a) = a := λ a, (classical.some_spec (h a)).symm,
  refine rel_hom.well_founded { to_fun := f, map_rel' := _ } DCC_dvd.well_founded_dvd_not_unit,
  intros a b h, rw [← hf a, ← hf b] at h, split,
  { contrapose! h, apply not_lt_of_le, rw h,
    apply mk_le_mk_of_dvd, apply (dvd_zero _), },
  have h1 := le_of_lt h, rw mk_le_mk_iff_dvd_iff at h1, cases h1 with x hx, use x,
  split, swap, {exact hx},
  contrapose! h, rcases h with ⟨u, rfl⟩, rw mk_eq_mk_iff_associated.2 ⟨_, hx.symm⟩,
  apply lt_irrefl,
end

local attribute [elab_as_eliminator] well_founded.fix

lemma exists_irreducible_factor {a : α} (ha : ¬ is_unit a) (ha0 : a ≠ 0) :
  ∃ i, irreducible i ∧ i ∣ a :=
(irreducible_or_factor a ha).elim (λ hai, ⟨a, hai, dvd_refl _⟩)
  (well_founded.fix
    DCC_dvd.well_founded_dvd_not_unit
    (λ a ih ha ha0 ⟨x, y, hx, hy, hxy⟩,
      have hx0 : x ≠ 0, from λ hx0, ha0 (by rw [← hxy, hx0, zero_mul]),
      (irreducible_or_factor x hx).elim
        (λ hxi, ⟨x, hxi, hxy ▸ by simp⟩)
        (λ hxf, let ⟨i, hi⟩ := ih x ⟨hx0, y, hy, hxy.symm⟩ hx hx0 hxf in
          ⟨i, hi.1, dvd.trans hi.2 (hxy ▸ by simp)⟩)) a ha ha0)

@[elab_as_eliminator] lemma induction_on_irreducible {P : α → Prop} (a : α)
  (h0 : P 0) (hu : ∀ u : α, is_unit u → P u)
  (hi : ∀ a i : α, a ≠ 0 → irreducible i → P a → P (i * a)) :
  P a :=
by haveI := classical.dec; exact
well_founded.fix DCC_dvd.well_founded_dvd_not_unit
  (λ a ih, if ha0 : a = 0 then ha0.symm ▸ h0
    else if hau : is_unit a then hu a hau
    else let ⟨i, hii, ⟨b, hb⟩⟩ := exists_irreducible_factor hau ha0 in
      have hb0 : b ≠ 0, from λ hb0, by simp * at *,
      hb.symm ▸ hi _ _ hb0 hii (ih _ ⟨hb0, i,
        hii.1, by rw [hb, mul_comm]⟩))
  a

lemma exists_factors (a : α) : a ≠ 0 →
  ∃f : multiset α, (∀b ∈ f, irreducible b) ∧ associated a f.prod :=
DCC_dvd.induction_on_irreducible a
  (λ h, (h rfl).elim)
  (λ u hu _, ⟨0, by simp [associated_one_iff_is_unit, hu]⟩)
  (λ a i ha0 hii ih hia0,
    let ⟨s, hs⟩ := ih ha0 in
    ⟨i::s, ⟨by clear _let_match; finish,
      by rw multiset.prod_cons;
        exact associated_mul_mul (by refl) hs.2⟩⟩)

end DCC_dvd

theorem DCC_dvd_of_well_founded_associates [comm_cancel_monoid_with_zero α]
  (h : well_founded ((<) : associates α → associates α → Prop)): DCC_dvd α :=
⟨by { refine rel_hom.well_founded _ h,
  exact { to_fun := associates.mk,
    map_rel' := λ a b ⟨ane0, ⟨c, ⟨hc, bac⟩⟩⟩,
      by { rw bac, apply lt_of_le_of_ne (associates.mk_le_mk_of_dvd (dvd.intro c rfl)),
        intro con, rw associates.mk_eq_mk_iff_associated at con, apply hc,
        rw ← associated_one_iff_is_unit, symmetry, apply associated_mul_left_cancel,
        convert con, apply mul_one, refl, exact ane0, }}}⟩

theorem DCC_dvd_iff_well_founded_associates [comm_cancel_monoid_with_zero α] :
  DCC_dvd α ↔ well_founded ((<) : associates α → associates α → Prop) :=
⟨by apply DCC_dvd.well_founded_associates, DCC_dvd_of_well_founded_associates⟩

/-- Unique factorization domains.

In a unique factorization domain each element (except zero) is uniquely
represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

This is equivalent to defining a unique factorization domain as a domain in
which each element (except zero) is non-uniquely represented as a multiset
of prime factors. This definition is used.

To define a UFD using the traditional definition in terms of multisets
of irreducible factors, use the definition `of_unique_irreducible_factorization`

-/
class unique_factorization_domain (α : Type*) [integral_domain α] :=
(factors : α → multiset α)
(factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
(prime_factors : ∀{a : α}, a ≠ 0 → ∀x∈factors a, prime x)

namespace unique_factorization_domain

variables [integral_domain α] [unique_factorization_domain α]

@[elab_as_eliminator] lemma induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a :=
by haveI := classical.dec_eq α; exact
if ha0 : a = 0 then ha0.symm ▸ h₁
else @multiset.induction_on _
  (λ s : multiset α, ∀ (a : α), a ≠ 0 → s.prod ~ᵤ a → (∀ p ∈ s, prime p) →  P a)
  (factors a)
  (λ _ _ h _, h₂ _ ((is_unit_iff_of_associated h.symm).2 is_unit_one))
  (λ p s ih a ha0 ⟨u, hu⟩ hsp,
    have ha : a = (p * u) * s.prod, by simp [hu.symm, mul_comm, mul_assoc],
    have hs0 : s.prod ≠ 0, from λ _ : s.prod = 0, by simp * at *,
    ha.symm ▸ h₃ _ _ hs0
      (prime_of_associated ⟨u, rfl⟩ (hsp p (multiset.mem_cons_self _ _)))
      (ih _ hs0 (by refl) (λ p hp, hsp p (multiset.mem_cons.2 (or.inr hp)))))
  _
  ha0
  (factors_prod ha0)
  (prime_factors ha0)

lemma factors_irreducible {a : α} (ha : irreducible a) :
  ∃ p, a ~ᵤ p ∧ factors a = p :: 0 :=
by haveI := classical.dec_eq α; exact
multiset.induction_on (factors a)
  (λ h, (ha.1 (associated_one_iff_is_unit.1 h.symm)).elim)
  (λ p s _ hp hs, let ⟨u, hu⟩ := hp in ⟨p,
    have hs0 : s = 0, from classical.by_contradiction
      (λ hs0, let ⟨q, hq⟩ := multiset.exists_mem_of_ne_zero hs0 in
       (hs q (by simp [hq])).2.1 $
        (ha.2 ((p * u) * (s.erase q).prod) _
          (by rw [mul_right_comm _ _ q, mul_assoc, ← multiset.prod_cons,
            multiset.cons_erase hq]; simp [hu.symm, mul_comm, mul_assoc])).resolve_left $
              mt is_unit_of_mul_is_unit_left $ mt is_unit_of_mul_is_unit_left
                (hs p (multiset.mem_cons_self _ _)).2.1),
    ⟨associated.symm (by clear _let_match; simp * at *), hs0 ▸ rfl⟩⟩)
  (factors_prod ha.ne_zero)
  (prime_factors ha.ne_zero)

lemma irreducible_iff_prime {p : α} : irreducible p ↔ prime p :=
by letI := classical.dec_eq α; exact
if hp0 : p = 0 then by simp [hp0]
else
  ⟨λ h, let ⟨q, hq⟩ := factors_irreducible h in
      have prime q, from hq.2 ▸ prime_factors hp0 _ (by simp [hq.2]),
      suffices prime (factors p).prod,
        from prime_of_associated (factors_prod hp0) this,
      hq.2.symm ▸ by simp [this],
    irreducible_of_prime⟩

lemma irreducible_factors : ∀{a : α}, a ≠ 0 → ∀x∈factors a, irreducible x :=
by simp only [irreducible_iff_prime]; exact @prime_factors _ _ _

lemma unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
      multiset.eq_zero_of_forall_not_mem (λ x hx,
        have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
        (hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
          (is_unit_iff_dvd_one.1 this)))))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (irreducible_iff_prime.1 (hf p (by simp)))
      (λ q hq, irreducible_iff_prime.1 (hg _ hq)) $
        (dvd_iff_dvd_of_rel_right hfg).1
          (show p ∣ (p :: f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated_mul_left_cancel
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero))
    end)

end unique_factorization_domain

structure unique_irreducible_factorization (α : Type*) [integral_domain α] :=
(factors : α → multiset α)
(factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
(irreducible_factors : ∀{a : α}, a ≠ 0 →  ∀x∈factors a, irreducible x)
(unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g)

namespace unique_factorization_domain
open unique_factorization_domain associated
variables [integral_domain α] [unique_factorization_domain α]

lemma exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a →
  ∃ q ∈ factors a, p ~ᵤ q :=
λ ⟨b, hb⟩,
have hb0 : b ≠ 0, from λ hb0, by simp * at *,
have multiset.rel associated (p :: factors b) (factors a),
  from unique
    (λ x hx, (multiset.mem_cons.1 hx).elim (λ h, h.symm ▸ hp)
      (irreducible_factors hb0 _))
    (irreducible_factors ha0)
    (associated.symm $ calc multiset.prod (factors a) ~ᵤ a : factors_prod ha0
      ... = p * b : hb
      ... ~ᵤ multiset.prod (p :: factors b) :
        by rw multiset.prod_cons; exact associated_mul_mul
          (associated.refl _)
          (associated.symm (factors_prod hb0))),
multiset.exists_mem_of_rel_of_mem this (by simp)

def of_unique_irreducible_factorization {α : Type*} [integral_domain α]
  (o : unique_irreducible_factorization α) : unique_factorization_domain α :=
{ prime_factors := by letI := classical.dec_eq α; exact λ a h p (hpa : p ∈ o.factors a),
    have hpi : irreducible p, from o.irreducible_factors h _ hpa,
    ⟨hpi.ne_zero, hpi.1,
      λ a b ⟨x, hx⟩,
      if hab0 : a * b = 0
      then (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim
        (λ ha0, by simp [ha0])
        (λ hb0, by simp [hb0])
      else
        have hx0 : x ≠ 0, from λ hx0, by simp * at *,
        have ha0 : a ≠ 0, from left_ne_zero_of_mul hab0,
        have hb0 : b ≠ 0, from right_ne_zero_of_mul hab0,
        have multiset.rel associated  (p :: o.factors x) (o.factors a + o.factors b),
          from o.unique
            (λ i hi, (multiset.mem_cons.1 hi).elim
              (λ hip, hip.symm ▸ hpi)
              (o.irreducible_factors hx0 _))
            (show ∀ x ∈ o.factors a + o.factors b, irreducible x,
              from λ x hx, (multiset.mem_add.1 hx).elim
                (o.irreducible_factors ha0 _)
                (o.irreducible_factors hb0 _)) $
              calc multiset.prod (p :: o.factors x)
                  ~ᵤ a * b : by rw [hx, multiset.prod_cons];
                    exact associated_mul_mul (by refl)
                      (o.factors_prod hx0)
              ... ~ᵤ (o.factors a).prod * (o.factors b).prod :
                associated_mul_mul
                  (o.factors_prod ha0).symm
                  (o.factors_prod hb0).symm
              ... = _ : by rw multiset.prod_add,
        let ⟨q, hqf, hq⟩ := multiset.exists_mem_of_rel_of_mem this
          (multiset.mem_cons_self p _) in
        (multiset.mem_add.1 hqf).elim
          (λ hqa, or.inl $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right (o.factors_prod ha0)).1
              (multiset.dvd_prod hqa))
          (λ hqb, or.inr $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right (o.factors_prod hb0)).1
              (multiset.dvd_prod hqb))⟩,
  ..o }

end unique_factorization_domain

namespace associates
open unique_factorization_domain associated
variables [integral_domain α]

/-- `factor_set α` representation elements of unique factorization domain as multisets.

`multiset α` produced by `factors` are only unique up to associated elements, while the multisets in
`factor_set α` are unqiue by equality and restricted to irreducible elements. This gives us a
representation of each element as a unique multisets (or the added ⊤ for 0), which has a complete
lattice struture. Infimum is the greatest common divisor and supremum is the least common multiple.
-/
@[reducible] def {u} factor_set (α : Type u) [integral_domain α] :
  Type u :=
with_top (multiset { a : associates α // irreducible a })

local attribute [instance] associated.setoid

theorem factor_set.coe_add {a b : multiset { a : associates α // irreducible a }} :
  (↑(a + b) : factor_set α) = a + b :=
by norm_cast

lemma factor_set.sup_add_inf_eq_add [decidable_eq (associates α)] :
  ∀(a b : factor_set α), a ⊔ b + a ⊓ b = a + b
| none     b        := show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b, by simp
| a        none     := show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤, by simp
| (some a) (some b) := show (a : factor_set α) ⊔ b + a ⊓ b = a + b, from
  begin
    rw [← with_top.coe_sup, ← with_top.coe_inf, ← with_top.coe_add, ← with_top.coe_add,
      with_top.coe_eq_coe],
    exact multiset.union_add_inter _ _
  end

def factor_set.prod : factor_set α → associates α
| none     := 0
| (some s) := (s.map coe).prod

@[simp] theorem prod_top : (⊤ : factor_set α).prod = 0 := rfl

@[simp] theorem prod_coe {s : multiset { a : associates α // irreducible a }} :
  (s : factor_set α).prod = (s.map coe).prod :=
rfl

@[simp] theorem prod_add : ∀(a b : factor_set α), (a + b).prod = a.prod * b.prod
| none b    := show (⊤ + b).prod = (⊤:factor_set α).prod * b.prod, by simp
| a    none := show (a + ⊤).prod = a.prod * (⊤:factor_set α).prod, by simp
| (some a) (some b) :=
  show (↑a + ↑b:factor_set α).prod = (↑a:factor_set α).prod * (↑b:factor_set α).prod,
    by rw [← factor_set.coe_add, prod_coe, prod_coe, prod_coe, multiset.map_add, multiset.prod_add]

theorem prod_mono : ∀{a b : factor_set α}, a ≤ b → a.prod ≤ b.prod
| none b h := have b = ⊤, from top_unique h, by rw [this, prod_top]; exact le_refl _
| a none h := show a.prod ≤ (⊤ : factor_set α).prod, by simp; exact le_top
| (some a) (some b) h := prod_le_prod $ multiset.map_le_map $ with_top.coe_le_coe.1 $ h

variable [unique_factorization_domain α]

theorem unique' {p q : multiset (associates α)} :
  (∀a∈p, irreducible a) → (∀a∈q, irreducible a) → p.prod = q.prod → p = q :=
begin
  apply multiset.induction_on_multiset_quot p,
  apply multiset.induction_on_multiset_quot q,
  assume s t hs ht eq,
  refine multiset.map_mk_eq_map_mk_of_rel (unique_factorization_domain.unique _ _ _),
  { exact assume a ha, ((irreducible_mk_iff _).1 $ hs _ $ multiset.mem_map_of_mem _ ha) },
  { exact assume a ha, ((irreducible_mk_iff _).1 $ ht _ $ multiset.mem_map_of_mem _ ha) },
  simpa [quot_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated] using eq
end

private theorem forall_map_mk_factors_irreducible (x : α) (hx : x ≠ 0) :
  ∀(a : associates α), a ∈ multiset.map associates.mk (factors x) → irreducible a :=
begin
  assume a ha,
  rcases multiset.mem_map.1 ha with ⟨c, hc, rfl⟩,
  exact (irreducible_mk_iff c).2 (irreducible_factors hx _ hc)
end

theorem prod_le_prod_iff_le {p q : multiset (associates α)}
  (hp : ∀a∈p, irreducible a) (hq : ∀a∈q, irreducible a) :
  p.prod ≤ q.prod ↔ p ≤ q :=
iff.intro
  begin
    rintros ⟨⟨c⟩, eqc⟩,
    have : c ≠ 0, from (mt mk_eq_zero.2 $
      assume (hc : quot.mk setoid.r c = 0),
      have (0 : associates α) ∈ q, from prod_eq_zero_iff.1 $ eqc.symm ▸ hc.symm ▸ mul_zero _,
      not_irreducible_zero ((irreducible_mk_iff 0).1 $ hq _ this)),
    have : associates.mk (factors c).prod = quot.mk setoid.r c,
      from mk_eq_mk_iff_associated.2 (factors_prod this),

    refine le_iff_exists_add.2 ⟨(factors c).map associates.mk, unique' hq _ _⟩,
    { assume x hx,
      rcases multiset.mem_add.1 hx with h | h,
      exact hp x h,
      exact forall_map_mk_factors_irreducible c ‹c ≠ 0› _ h },
    { simp [multiset.prod_add, prod_mk, *] at * }
  end
  prod_le_prod

def factors' (a : α) (ha : a ≠ 0) : multiset { a : associates α // irreducible a } :=
(factors a).pmap (λa ha, ⟨associates.mk a, (irreducible_mk_iff _).2 ha⟩)
  (irreducible_factors $ ha)

@[simp] theorem map_subtype_coe_factors' {a : α} (ha : a ≠ 0) :
  (factors' a ha).map coe = (factors a).map associates.mk :=
by simp [factors', multiset.map_pmap, multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ~ᵤ b) :
  factors' a ha = factors' b hb :=
have multiset.rel associated (factors a) (factors b), from
  unique (irreducible_factors ha) (irreducible_factors hb)
    ((factors_prod ha).trans $ h.trans $ (factors_prod hb).symm),
by simpa [(multiset.map_eq_map subtype.coe_injective).symm, rel_associated_iff_map_eq_map.symm]

variable [dec : decidable_eq (associates α)]
include dec

def factors (a : associates α) : factor_set α :=
begin
  refine (if h : a = 0 then ⊤ else
    quotient.hrec_on a (λx h, some $ factors' x (mt mk_eq_zero.2 h)) _ h),

  assume a b hab,
  apply function.hfunext,
  { have : a ~ᵤ 0 ↔ b ~ᵤ 0, from
      iff.intro (assume ha0, hab.symm.trans ha0) (assume hb0, hab.trans hb0),
    simp only [associated_zero_iff_eq_zero] at this,
    simp only [quotient_mk_eq_mk, this, mk_eq_zero] },
  exact (assume ha hb eq, heq_of_eq $ congr_arg some $ factors'_cong _ _ hab)
end

@[simp] theorem factors_0 : (0 : associates α).factors = ⊤ :=
dif_pos rfl

@[simp] theorem factors_mk (a : α) (h : a ≠ 0) : (associates.mk a).factors = factors' a h :=
dif_neg (mt mk_eq_zero.1 h)

theorem prod_factors : ∀(s : factor_set α), s.prod.factors = s
| none     := by simp [factor_set.prod]; refl
| (some s) :=
  begin
    unfold factor_set.prod,
    generalize eq_a : (s.map coe).prod = a,
    rcases a with ⟨a⟩,
    rw quot_mk_eq_mk at *,

    have : (s.map (coe : _ → associates α)).prod ≠ 0, from assume ha,
      let ⟨⟨a, ha⟩, h, eq⟩ := multiset.mem_map.1 (prod_eq_zero_iff.1 ha) in
      have irreducible (0 : associates α), from eq ▸ ha,
      not_irreducible_zero ((irreducible_mk_iff _).1 this),
    have ha : a ≠ 0, by simp [*] at *,
    suffices : (unique_factorization_domain.factors a).map associates.mk = s.map coe,
    { rw [factors_mk a ha],
      apply congr_arg some _,
      simpa [(multiset.map_eq_map subtype.coe_injective).symm] },

    refine unique'
      (forall_map_mk_factors_irreducible _ ha)
      (assume a ha, let ⟨⟨x, hx⟩, ha, eq⟩ := multiset.mem_map.1 ha in eq ▸ hx)
      _,
    rw [prod_mk, eq_a, mk_eq_mk_iff_associated],
    exact factors_prod ha
  end

theorem factors_prod (a : associates α) : a.factors.prod = a :=
quotient.induction_on a $ assume a, decidable.by_cases
  (assume : associates.mk a = 0, by simp [quotient_mk_eq_mk, this])
  (assume : associates.mk a ≠ 0,
    have a ≠ 0, by simp * at *,
    by simp [this, quotient_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated.2 (factors_prod this)])

theorem eq_of_factors_eq_factors {a b : associates α} (h : a.factors = b.factors) : a = b :=
have a.factors.prod = b.factors.prod, by rw h,
by rwa [factors_prod, factors_prod] at this

omit dec

theorem eq_of_prod_eq_prod {a b : factor_set α} (h : a.prod = b.prod) : a = b :=
begin
  classical,
  have : a.prod.factors = b.prod.factors, by rw h,
  rwa [prod_factors, prod_factors] at this
end

include dec


@[simp] theorem factors_mul (a b : associates α) : (a * b).factors = a.factors + b.factors :=
eq_of_prod_eq_prod $ eq_of_factors_eq_factors $
  by rw [prod_add, factors_prod, factors_prod, factors_prod]

theorem factors_mono : ∀{a b : associates α}, a ≤ b → a.factors ≤ b.factors
| s t ⟨d, rfl⟩ := by rw [factors_mul] ; exact le_add_of_nonneg_right bot_le

theorem factors_le {a b : associates α} : a.factors ≤ b.factors ↔ a ≤ b :=
iff.intro
  (assume h, have a.factors.prod ≤ b.factors.prod, from prod_mono h,
    by rwa [factors_prod, factors_prod] at this)
  factors_mono

omit dec

theorem prod_le {a b : factor_set α} : a.prod ≤ b.prod ↔ a ≤ b :=
begin
  classical,
  exact iff.intro
  (assume h, have a.prod.factors ≤ b.prod.factors, from factors_mono h,
    by rwa [prod_factors, prod_factors] at this)
  prod_mono
end

include dec

instance : has_sup (associates α) := ⟨λa b, (a.factors ⊔ b.factors).prod⟩
instance : has_inf (associates α) := ⟨λa b, (a.factors ⊓ b.factors).prod⟩

instance : bounded_lattice (associates α) :=
{ sup          := (⊔),
  inf          := (⊓),
  sup_le       :=
    assume a b c hac hbc, factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc)),
  le_sup_left  := assume a b,
    le_trans (le_of_eq (factors_prod a).symm) $ prod_mono $ le_sup_left,
  le_sup_right := assume a b,
    le_trans (le_of_eq (factors_prod b).symm) $ prod_mono $ le_sup_right,
  le_inf :=
    assume a b c hac hbc, factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc)),
  inf_le_left  := assume a b,
    le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a)),
  inf_le_right := assume a b,
    le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)),
  .. associates.partial_order,
  .. associates.order_top,
  .. associates.order_bot }

lemma sup_mul_inf (a b : associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b,
begin
  refine eq_of_factors_eq_factors _,
  rw [← prod_add, prod_factors, factors_mul, factor_set.sup_add_inf_eq_add]
end

end associates

section
open associates unique_factorization_domain

/-- `to_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
def unique_factorization_domain.to_gcd_monoid
  (α : Type*) [integral_domain α] [unique_factorization_domain α] [normalization_monoid α]
  [decidable_eq (associates α)] : gcd_monoid α :=
{ gcd := λa b, (associates.mk a ⊓ associates.mk b).out,
  lcm := λa b, (associates.mk a ⊔ associates.mk b).out,
  gcd_dvd_left := assume a b, (out_dvd_iff a (associates.mk a ⊓ associates.mk b)).2 $ inf_le_left,
  gcd_dvd_right := assume a b, (out_dvd_iff b (associates.mk a ⊓ associates.mk b)).2 $ inf_le_right,
  dvd_gcd := assume a b c hac hab, show a ∣ (associates.mk c ⊓ associates.mk b).out,
    by rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]; exact ⟨hac, hab⟩,
  lcm_zero_left := assume a, show (⊤ ⊔ associates.mk a).out = 0, by simp,
  lcm_zero_right := assume a, show (associates.mk a ⊔ ⊤).out = 0, by simp,
  gcd_mul_lcm := assume a b,
    show (associates.mk a ⊓ associates.mk b).out * (associates.mk a ⊔ associates.mk b).out =
      normalize (a * b),
    by rw [← out_mk, ← out_mul, mul_comm, sup_mul_inf]; refl,
  normalize_gcd := assume a b, by convert normalize_out _,
  .. ‹normalization_monoid α› }

end

namespace unique_factorization_domain

variables {R : Type*} [integral_domain R] [unique_factorization_domain R]

lemma no_factors_of_no_prime_factors {a b : R} (ha : a ≠ 0)
  (h : (∀ {d}, d ∣ a → d ∣ b → ¬ prime d)) : ∀ {d}, d ∣ a → d ∣ b → is_unit d :=
λ d, induction_on_prime d
  (by { simp only [zero_dvd_iff], intros, contradiction })
  (λ x hx _ _, hx)
  (λ d q hp hq ih dvd_a dvd_b,
    absurd hq (h (dvd_of_mul_right_dvd dvd_a) (dvd_of_mul_right_dvd dvd_b)))

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
lemma dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0) :
  (∀ {d}, d ∣ a → d ∣ c → ¬ prime d) → a ∣ b * c → a ∣ b :=
begin
  refine induction_on_prime c _ _ _,
  { intro no_factors,
    simp only [dvd_zero, mul_zero, forall_prop_of_true],
    haveI := classical.prop_decidable,
    exact is_unit_iff_forall_dvd.mp
      (no_factors_of_no_prime_factors ha @no_factors (dvd_refl a) (dvd_zero a)) _ },
  { rintros _ ⟨x, rfl⟩ _ a_dvd_bx,
    apply units.dvd_mul_right.mp a_dvd_bx },
  { intros c p hc hp ih no_factors a_dvd_bpc,
    apply ih (λ q dvd_a dvd_c hq, no_factors dvd_a (dvd_mul_of_dvd_right dvd_c _) hq),
    rw mul_left_comm at a_dvd_bpc,
    refine or.resolve_left (left_dvd_or_dvd_right_of_dvd_prime_mul hp a_dvd_bpc) (λ h, _),
    exact no_factors h (dvd_mul_right p c) hp }
end

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
lemma dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
  (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬ prime d) : a ∣ b * c → a ∣ c :=
by simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
lemma exists_reduced_factors : ∀ (a ≠ (0 : R)) b,
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
begin
  haveI := classical.prop_decidable,
  intros a,
  refine induction_on_prime a _ _ _,
  { intros, contradiction },
  { intros a a_unit a_ne_zero b,
    use [a, b, 1],
    split,
    { intros p p_dvd_a _,
      exact is_unit_of_dvd_unit p_dvd_a a_unit },
    { simp } },
  { intros a p a_ne_zero p_prime ih_a pa_ne_zero b,
    by_cases p ∣ b,
    { rcases h with ⟨b, rfl⟩,
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b,
      refine ⟨a', b', p * c', @no_factor, _, _⟩,
      { rw [mul_assoc, ha'] },
      { rw [mul_assoc, hb'] } },
    { obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b,
      refine ⟨p * a', b', c', _, mul_left_comm _ _ _, rfl⟩,
      intros q q_dvd_pa' q_dvd_b',
      cases left_dvd_or_dvd_right_of_dvd_prime_mul p_prime q_dvd_pa' with p_dvd_q q_dvd_a',
      { have : p ∣ c' * b' := dvd_mul_of_dvd_right (dvd_trans p_dvd_q q_dvd_b') _,
        contradiction },
      exact coprime q_dvd_a' q_dvd_b'  } }
end

lemma exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
in ⟨a', b', c', λ _ hpb hpa, no_factor hpa hpb, ha, hb⟩

end unique_factorization_domain
