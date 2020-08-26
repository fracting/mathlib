/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import measure_theory.measure_space
import topology.instances.ennreal
import analysis.normed_space.basic

/-!
# Borel (measurable) space

## Main definitions

* `borel α` : the least `σ`-algebra that contains all open sets;
* `class borel_space` : a space with `topological_space` and `measurable_space` structures
  such that `‹measurable_space α› = borel α`;
* `class opens_measurable_space` : a space with `topological_space` and `measurable_space`
  structures such that all open sets are measurable; equivalently, `borel α ≤ ‹measurable_space α›`.
* `borel_space` instances on `empty`, `unit`, `bool`, `nat`, `int`, `rat`;
* `measurable` and `borel_space` instances on `ℝ`, `ℝ≥0`, `ennreal`.
* A measure is `regular` if it is finite on compact sets, inner regular and outer regular.

## Main statements

* `is_open.is_measurable`, `is_closed.is_measurable`: open and closed sets are measurable;
* `continuous.measurable` : a continuous function is measurable;
* `continuous.measurable2` : if `f : α → β` and `g : α → γ` are measurable and `op : β × γ → δ`
  is continuous, then `λ x, op (f x, g y)` is measurable;
* `measurable.add` etc : dot notation for arithmetic operations on `measurable` predicates,
  and similarly for `dist` and `edist`;
* `measurable.ennreal*` : special cases for arithmetic operations on `ennreal`s.
-/

noncomputable theory

open classical set
open_locale classical big_operators topological_space

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y} {s t u : set α}

open measurable_space topological_space

/-- `measurable_space` structure generated by `topological_space`. -/
def borel (α : Type u) [topological_space α] : measurable_space α :=
generate_from {s : set α | is_open s}

lemma borel_eq_top_of_discrete [topological_space α] [discrete_topology α] :
  borel α = ⊤ :=
top_le_iff.1 $ λ s hs, generate_measurable.basic s (is_open_discrete s)

lemma borel_eq_top_of_encodable [topological_space α] [t1_space α] [encodable α] :
  borel α = ⊤ :=
begin
  refine (top_le_iff.1 $ λ s hs, bUnion_of_singleton s ▸ _),
  apply is_measurable.bUnion s.countable_encodable,
  intros x hx,
  apply is_measurable.of_compl,
  apply generate_measurable.basic,
  exact is_closed_singleton
end

lemma borel_eq_generate_from_of_subbasis {s : set (set α)}
  [t : topological_space α] [second_countable_topology α] (hs : t = generate_from s) :
  borel α = generate_from s :=
le_antisymm
  (generate_from_le $ assume u (hu : t.is_open u),
    begin
      rw [hs] at hu,
      induction hu,
      case generate_open.basic : u hu
      { exact generate_measurable.basic u hu },
      case generate_open.univ
      { exact @is_measurable.univ α (generate_from s) },
      case generate_open.inter : s₁ s₂ _ _ hs₁ hs₂
      { exact @is_measurable.inter α (generate_from s) _ _ hs₁ hs₂ },
      case generate_open.sUnion : f hf ih {
        rcases is_open_sUnion_countable f (by rwa hs) with ⟨v, hv, vf, vu⟩,
        rw ← vu,
        exact @is_measurable.sUnion α (generate_from s) _ hv
          (λ x xv, ih _ (vf xv)) }
    end)
  (generate_from_le $ assume u hu, generate_measurable.basic _ $
    show t.is_open u, by rw [hs]; exact generate_open.basic _ hu)

lemma borel_eq_generate_Iio (α)
  [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α] :
  borel α = generate_from (range Iio) :=
begin
  refine le_antisymm _ (generate_from_le _),
  { rw borel_eq_generate_from_of_subbasis (@order_topology.topology_eq_generate_intervals α _ _ _),
    letI : measurable_space α := measurable_space.generate_from (range Iio),
    have H : ∀ a:α, is_measurable (Iio a) := λ a, generate_measurable.basic _ ⟨_, rfl⟩,
    refine generate_from_le _, rintro _ ⟨a, rfl | rfl⟩; [skip, apply H],
    by_cases h : ∃ a', ∀ b, a < b ↔ a' ≤ b,
    { rcases h with ⟨a', ha'⟩,
      rw (_ : Ioi a = (Iio a')ᶜ), { exact (H _).compl },
      simp [set.ext_iff, ha'] },
    { rcases is_open_Union_countable
        (λ a' : {a' : α // a < a'}, {b | a'.1 < b})
        (λ a', is_open_lt' _) with ⟨v, ⟨hv⟩, vu⟩,
      simp [set.ext_iff] at vu,
      have : Ioi a = ⋃ x : v, (Iio x.1.1)ᶜ,
      { simp [set.ext_iff],
        refine λ x, ⟨λ ax, _, λ ⟨a', ⟨h, av⟩, ax⟩, lt_of_lt_of_le h ax⟩,
        rcases (vu x).2 _ with ⟨a', h₁, h₂⟩,
        { exact ⟨a', h₁, le_of_lt h₂⟩ },
        refine not_imp_comm.1 (λ h, _) h,
        exact ⟨x, λ b, ⟨λ ab, le_of_not_lt (λ h', h ⟨b, ab, h'⟩),
          lt_of_lt_of_le ax⟩⟩ },
      rw this, resetI,
      apply is_measurable.Union,
      exact λ _, (H _).compl } },
  { simp, rintro _ a rfl,
    exact generate_measurable.basic _ is_open_Iio }
end

lemma borel_eq_generate_Ioi (α)
  [topological_space α] [h : second_countable_topology α]
  [linear_order α] [order_topology α] :
  borel α = generate_from (range Ioi) :=
@borel_eq_generate_Iio (order_dual α) _ h _ _

lemma borel_comap {f : α → β} {t : topological_space β} :
  @borel α (t.induced f) = (@borel β t).comap f :=
comap_generate_from.symm

lemma continuous.borel_measurable [topological_space α] [topological_space β]
  {f : α → β} (hf : continuous f) :
  @measurable α β (borel α) (borel β) f :=
measurable.of_le_map $ generate_from_le $
  λ s hs, generate_measurable.basic (f ⁻¹' s) (hf s hs)

/-- A space with `measurable_space` and `topological_space` structures such that
all open sets are measurable. -/
class opens_measurable_space (α : Type*) [topological_space α] [h : measurable_space α] : Prop :=
(borel_le : borel α ≤ h)

/-- A space with `measurable_space` and `topological_space` structures such that
the `σ`-algebra of measurable sets is exactly the `σ`-algebra generated by open sets. -/
class borel_space (α : Type*) [topological_space α] [measurable_space α] : Prop :=
(measurable_eq : ‹measurable_space α› = borel α)

/-- In a `borel_space` all open sets are measurable. -/
@[priority 100]
instance borel_space.opens_measurable {α : Type*} [topological_space α] [measurable_space α]
  [borel_space α] : opens_measurable_space α :=
⟨ge_of_eq $ borel_space.measurable_eq⟩

instance subtype.borel_space {α : Type*} [topological_space α] [measurable_space α]
  [hα : borel_space α] (s : set α) :
  borel_space s :=
⟨by { rw [hα.1, subtype.measurable_space, ← borel_comap], refl }⟩

instance subtype.opens_measurable_space {α : Type*} [topological_space α] [measurable_space α]
  [h : opens_measurable_space α] (s : set α) :
  opens_measurable_space s :=
⟨by { rw [borel_comap], exact comap_mono h.1 }⟩

section
variables [topological_space α] [measurable_space α] [opens_measurable_space α]
   [topological_space β] [measurable_space β] [opens_measurable_space β]
   [topological_space γ] [measurable_space γ] [borel_space γ]
   [measurable_space δ]

lemma is_open.is_measurable (h : is_open s) : is_measurable s :=
opens_measurable_space.borel_le _ $ generate_measurable.basic _ h

lemma is_measurable_interior : is_measurable (interior s) := is_open_interior.is_measurable

lemma is_closed.is_measurable (h : is_closed s) : is_measurable s :=
is_measurable.compl_iff.1 $ h.is_measurable

lemma is_compact.is_measurable [t2_space α] (h : is_compact s) : is_measurable s :=
h.is_closed.is_measurable

lemma is_measurable_closure : is_measurable (closure s) :=
is_closed_closure.is_measurable

instance nhds_is_measurably_generated (a : α) : (𝓝 a).is_measurably_generated :=
begin
  rw [nhds, infi_subtype'],
  refine @filter.infi_is_measurably_generated _ _ _ _ (λ i, _),
  exact i.2.2.is_measurable.principal_is_measurably_generated
end

/-- If `s` is a measurable set, then `𝓝[s] a` is a measurably generated filter for
each `a`. This cannot be an `instance` because it depends on a non-instance `hs : is_measurable s`.
-/
lemma is_measurable.nhds_within_is_measurably_generated {s : set α} (hs : is_measurable s) (a : α) :
  (𝓝[s] a).is_measurably_generated :=
by haveI := hs.principal_is_measurably_generated; exact filter.inf_is_measurably_generated _ _

@[priority 100] -- see Note [lower instance priority]
instance opens_measurable_space.to_measurable_singleton_class [t1_space α] :
  measurable_singleton_class α :=
⟨λ x, is_closed_singleton.is_measurable⟩

section order_closed_topology
variables [preorder α] [order_closed_topology α] {a b : α}

lemma is_measurable_Ici : is_measurable (Ici a) := is_closed_Ici.is_measurable
lemma is_measurable_Iic : is_measurable (Iic a) := is_closed_Iic.is_measurable
lemma is_measurable_Icc : is_measurable (Icc a b) := is_closed_Icc.is_measurable

instance nhds_within_Ici_is_measurably_generated :
  (𝓝[Ici b] a).is_measurably_generated :=
is_measurable_Ici.nhds_within_is_measurably_generated _

instance nhds_within_Iic_is_measurably_generated :
  (𝓝[Iic b] a).is_measurably_generated :=
is_measurable_Iic.nhds_within_is_measurably_generated _

instance at_top_is_measurably_generated : (filter.at_top : filter α).is_measurably_generated :=
@filter.infi_is_measurably_generated _ _ _ _ $
  λ a, (is_measurable_Ici : is_measurable (Ici a)).principal_is_measurably_generated

instance at_bot_is_measurably_generated : (filter.at_bot : filter α).is_measurably_generated :=
@filter.infi_is_measurably_generated _ _ _ _ $
  λ a, (is_measurable_Iic : is_measurable (Iic a)).principal_is_measurably_generated

end order_closed_topology

section order_closed_topology
variables [linear_order α] [order_closed_topology α] {a b : α}

lemma is_measurable_Iio : is_measurable (Iio a) := is_open_Iio.is_measurable
lemma is_measurable_Ioi : is_measurable (Ioi a) := is_open_Ioi.is_measurable
lemma is_measurable_Ioo : is_measurable (Ioo a b) := is_open_Ioo.is_measurable
lemma is_measurable_Ioc : is_measurable (Ioc a b) := is_measurable_Ioi.inter is_measurable_Iic
lemma is_measurable_Ico : is_measurable (Ico a b) := is_measurable_Ici.inter is_measurable_Iio

instance nhds_within_Ioi_is_measurably_generated :
  (𝓝[Ioi b] a).is_measurably_generated :=
is_measurable_Ioi.nhds_within_is_measurably_generated _

instance nhds_within_Iio_is_measurably_generated :
  (𝓝[Iio b] a).is_measurably_generated :=
is_measurable_Iio.nhds_within_is_measurably_generated _

end order_closed_topology

lemma is_measurable_interval [decidable_linear_order α] [order_closed_topology α] {a b : α} :
  is_measurable (interval a b) :=
is_measurable_Icc

instance prod.opens_measurable_space [second_countable_topology α] [second_countable_topology β] :
  opens_measurable_space (α × β) :=
begin
  refine ⟨_⟩,
  rcases is_open_generated_countable_inter α with ⟨a, ha₁, ha₂, ha₃, ha₄, ha₅⟩,
  rcases is_open_generated_countable_inter β with ⟨b, hb₁, hb₂, hb₃, hb₄, hb₅⟩,
  have : prod.topological_space = generate_from {g | ∃u∈a, ∃v∈b, g = set.prod u v},
  { rw [ha₅, hb₅], exact prod_generate_from_generate_from_eq ha₄ hb₄ },
  rw [borel_eq_generate_from_of_subbasis this],
  apply generate_from_le,
  rintros _ ⟨u, hu, v, hv, rfl⟩,
  have hu : is_open u, by { rw [ha₅], exact generate_open.basic _ hu },
  have hv : is_open v, by { rw [hb₅], exact generate_open.basic _ hv },
  exact hu.is_measurable.prod hv.is_measurable
end

/-- A continuous function from an `opens_measurable_space` to a `borel_space`
is measurable. -/
lemma continuous.measurable {f : α → γ} (hf : continuous f) :
  measurable f :=
hf.borel_measurable.mono opens_measurable_space.borel_le
  (le_of_eq $ borel_space.measurable_eq)

/-- A homeomorphism between two Borel spaces is a measurable equivalence.-/
def homeomorph.to_measurable_equiv {α : Type*} {β : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [topological_space β] [measurable_space β]
  [borel_space β] (h : α ≃ₜ β) :
  measurable_equiv α β :=
{ measurable_to_fun := h.continuous_to_fun.measurable,
  measurable_inv_fun := h.continuous_inv_fun.measurable,
  .. h }

lemma measurable_of_continuous_on_compl_singleton [t1_space α] {f : α → γ} (a : α)
  (hf : continuous_on f {x | x ≠ a}) :
  measurable f :=
measurable_of_measurable_on_compl_singleton a
  (continuous_on_iff_continuous_restrict.1 hf).measurable

lemma continuous.measurable2 [second_countable_topology α] [second_countable_topology β]
  {f : δ → α} {g : δ → β} {c : α → β → γ}
  (h : continuous (λp:α×β, c p.1 p.2)) (hf : measurable f) (hg : measurable g) :
  measurable (λa, c (f a) (g a)) :=
h.measurable.comp (hf.prod_mk hg)

lemma measurable.smul [semiring α] [second_countable_topology α]
  [add_comm_monoid γ] [second_countable_topology γ]
  [semimodule α γ] [topological_semimodule α γ]
  {f : δ → α} {g : δ → γ} (hf : measurable f) (hg : measurable g) :
  measurable (λ c, f c • g c) :=
continuous_smul.measurable2 hf hg

lemma measurable.const_smul {α : Type*} [topological_space α] [semiring α]
  [add_comm_monoid γ] [semimodule α γ] [topological_semimodule α γ]
  {f : δ → γ} (hf : measurable f) (c : α) :
  measurable (λ x, c • f x) :=
(continuous_const.smul continuous_id).measurable.comp hf

lemma measurable_const_smul_iff {α : Type*} [topological_space α]
  [division_ring α] [add_comm_monoid γ]
  [semimodule α γ] [topological_semimodule α γ]
  {f : δ → γ} {c : α} (hc : c ≠ 0) :
  measurable (λ x, c • f x) ↔ measurable f :=
⟨λ h, by simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.const_smul c⁻¹,
  λ h, h.const_smul c⟩

lemma is_measurable_le' [partial_order α] [order_closed_topology α] [second_countable_topology α] :
  is_measurable {p : α × α | p.1 ≤ p.2} :=
order_closed_topology.is_closed_le'.is_measurable

lemma is_measurable_le [partial_order α] [order_closed_topology α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  is_measurable {a | f a ≤ g a} :=
hf.prod_mk hg is_measurable_le'

lemma measurable.max [decidable_linear_order α] [order_closed_topology α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  measurable (λa, max (f a) (g a)) :=
hf.piecewise (is_measurable_le hg hf) hg

lemma measurable.min [decidable_linear_order α] [order_closed_topology α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  measurable (λa, min (f a) (g a)) :=
hf.piecewise (is_measurable_le hf hg) hg

end

section borel_space
variables [topological_space α] [measurable_space α] [borel_space α]
  [topological_space β] [measurable_space β] [borel_space β]
  [topological_space γ] [measurable_space γ] [borel_space γ]
  [measurable_space δ]

lemma prod_le_borel_prod : prod.measurable_space ≤ borel (α × β) :=
begin
  rw [‹borel_space α›.measurable_eq, ‹borel_space β›.measurable_eq],
  refine sup_le _ _,
  { exact comap_le_iff_le_map.mpr continuous_fst.borel_measurable },
  { exact comap_le_iff_le_map.mpr continuous_snd.borel_measurable }
end

instance prod.borel_space [second_countable_topology α] [second_countable_topology β] :
  borel_space (α × β) :=
⟨le_antisymm prod_le_borel_prod opens_measurable_space.borel_le⟩

@[to_additive]
lemma measurable_mul [has_mul α] [has_continuous_mul α] [second_countable_topology α] :
  measurable (λ p : α × α, p.1 * p.2) :=
continuous_mul.measurable

@[to_additive]
lemma measurable.mul [has_mul α] [has_continuous_mul α] [second_countable_topology α]
  {f : δ → α} {g : δ → α} : measurable f → measurable g → measurable (λa, f a * g a) :=
continuous_mul.measurable2

@[to_additive]
lemma measurable_mul_left [has_mul α] [has_continuous_mul α] (x : α) :
  measurable (λ y : α, x * y) :=
continuous.measurable $ continuous_const.mul continuous_id

@[to_additive]
lemma measurable_mul_right [has_mul α] [has_continuous_mul α] (x : α) :
  measurable (λ y : α, y * x) :=
continuous.measurable $ continuous_id.mul continuous_const

@[to_additive]
lemma finset.measurable_prod {ι : Type*} [comm_monoid α] [has_continuous_mul α]
  [second_countable_topology α] {f : ι → δ → α} (s : finset ι) (hf : ∀i, measurable (f i)) :
  measurable (λa, ∏ i in s, f i a) :=
finset.induction_on s
  (by simp only [finset.prod_empty, measurable_const])
  (assume i s his ih, by simpa [his] using (hf i).mul ih)

@[to_additive]
lemma measurable_inv [group α] [topological_group α] : measurable (has_inv.inv : α → α) :=
continuous_inv.measurable

@[to_additive]
lemma measurable.inv [group α] [topological_group α] {f : δ → α} (hf : measurable f) :
  measurable (λa, (f a)⁻¹) :=
measurable_inv.comp hf

lemma measurable_inv' {α : Type*} [normed_field α] [measurable_space α] [borel_space α] :
  measurable (has_inv.inv : α → α) :=
measurable_of_continuous_on_compl_singleton 0 normed_field.continuous_on_inv

lemma measurable.inv' {α : Type*} [normed_field α] [measurable_space α] [borel_space α]
  {f : δ → α} (hf : measurable f) :
  measurable (λa, (f a)⁻¹) :=
measurable_inv'.comp hf

@[to_additive]
lemma measurable.of_inv [group α] [topological_group α] {f : δ → α}
  (hf : measurable (λ a, (f a)⁻¹)) : measurable f :=
by simpa only [inv_inv] using hf.inv

@[simp, to_additive]
lemma measurable_inv_iff [group α] [topological_group α] {f : δ → α} :
  measurable (λ a, (f a)⁻¹) ↔ measurable f :=
⟨measurable.of_inv, measurable.inv⟩

lemma measurable.sub [add_group α] [topological_add_group α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  measurable (λ x, f x - g x) :=
hf.add hg.neg

lemma measurable.is_lub [linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, measurable (f i))
  (hg : ∀ b, is_lub {a | ∃ i, f i b = a} (g b)) :
  measurable g :=
begin
  change ∀ b, is_lub (range $ λ i, f i b) (g b) at hg,
  rw [‹borel_space α›.measurable_eq, borel_eq_generate_Ioi α],
  apply measurable_generate_from,
  rintro _ ⟨a, rfl⟩,
  simp only [set.preimage, mem_Ioi, lt_is_lub_iff (hg _), exists_range_iff, set_of_exists],
  exact is_measurable.Union (λ i, hf i (is_open_lt' _).is_measurable)
end

lemma measurable.is_glb [linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, measurable (f i))
  (hg : ∀ b, is_glb {a | ∃ i, f i b = a} (g b)) :
  measurable g :=
begin
  change ∀ b, is_glb (range $ λ i, f i b) (g b) at hg,
  rw [‹borel_space α›.measurable_eq, borel_eq_generate_Iio α],
  apply measurable_generate_from,
  rintro _ ⟨a, rfl⟩,
  simp only [set.preimage, mem_Iio, is_glb_lt_iff (hg _), exists_range_iff, set_of_exists],
  exact is_measurable.Union (λ i, hf i (is_open_gt' _).is_measurable)
end

lemma measurable_supr [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨆ i, f i b) :=
measurable.is_lub hf $ λ b, is_lub_supr

lemma measurable_infi [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨅ i, f i b) :=
measurable.is_glb hf $ λ b, is_glb_infi

lemma measurable.supr_Prop {α} [measurable_space α] [complete_lattice α]
  (p : Prop) {f : δ → α} (hf : measurable f) :
  measurable (λ b, ⨆ h : p, f b) :=
classical.by_cases
  (assume h : p, begin convert hf, funext, exact supr_pos h end)
  (assume h : ¬p, begin convert measurable_const, funext, exact supr_neg h end)

lemma measurable.infi_Prop {α} [measurable_space α] [complete_lattice α]
  (p : Prop) {f : δ → α} (hf : measurable f) :
  measurable (λ b, ⨅ h : p, f b) :=
classical.by_cases
  (assume h : p, begin convert hf, funext, exact infi_pos h end )
  (assume h : ¬p, begin convert measurable_const, funext, exact infi_neg h end)

lemma measurable_bsupr [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] (p : ι → Prop) {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨆ i (hi : p i), f i b) :=
measurable_supr $ λ i, (hf i).supr_Prop (p i)

lemma measurable_binfi [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] (p : ι → Prop) {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨅ i (hi : p i), f i b) :=
measurable_infi $ λ i, (hf i).infi_Prop (p i)

/-- Convert a `homeomorph` to a `measurable_equiv`. -/
def homemorph.to_measurable_equiv (h : α ≃ₜ β) :
  measurable_equiv α β :=
{ to_equiv := h.to_equiv,
  measurable_to_fun := h.continuous_to_fun.measurable,
  measurable_inv_fun := h.continuous_inv_fun.measurable }

end borel_space

instance empty.borel_space : borel_space empty := ⟨borel_eq_top_of_discrete.symm⟩
instance unit.borel_space : borel_space unit := ⟨borel_eq_top_of_discrete.symm⟩
instance bool.borel_space : borel_space bool := ⟨borel_eq_top_of_discrete.symm⟩
instance nat.borel_space : borel_space ℕ := ⟨borel_eq_top_of_discrete.symm⟩
instance int.borel_space : borel_space ℤ := ⟨borel_eq_top_of_discrete.symm⟩
instance rat.borel_space : borel_space ℚ := ⟨borel_eq_top_of_encodable.symm⟩

instance real.measurable_space : measurable_space ℝ := borel ℝ
instance real.borel_space : borel_space ℝ := ⟨rfl⟩

instance nnreal.measurable_space : measurable_space nnreal := borel nnreal
instance nnreal.borel_space : borel_space nnreal := ⟨rfl⟩

instance ennreal.measurable_space : measurable_space ennreal := borel ennreal
instance ennreal.borel_space : borel_space ennreal := ⟨rfl⟩

section metric_space

variables [metric_space α] [measurable_space α] [opens_measurable_space α] {x : α} {ε : ℝ}

lemma is_measurable_ball : is_measurable (metric.ball x ε) :=
metric.is_open_ball.is_measurable

lemma is_measurable_closed_ball : is_measurable (metric.closed_ball x ε) :=
metric.is_closed_ball.is_measurable

lemma measurable_dist [second_countable_topology α] :
  measurable (λp:α×α, dist p.1 p.2) :=
continuous_dist.measurable

lemma measurable.dist [second_countable_topology α] [measurable_space β] {f g : β → α}
  (hf : measurable f) (hg : measurable g) : measurable (λ b, dist (f b) (g b)) :=
continuous_dist.measurable2 hf hg

lemma measurable_nndist [second_countable_topology α] : measurable (λp:α×α, nndist p.1 p.2) :=
continuous_nndist.measurable

lemma measurable.nndist [second_countable_topology α] [measurable_space β] {f g : β → α} :
  measurable f → measurable g → measurable (λ b, nndist (f b) (g b)) :=
continuous_nndist.measurable2

end metric_space

section emetric_space

variables [emetric_space α] [measurable_space α] [opens_measurable_space α] {x : α} {ε : ennreal}

lemma is_measurable_eball : is_measurable (emetric.ball x ε) :=
emetric.is_open_ball.is_measurable

lemma measurable_edist [second_countable_topology α] :
  measurable (λp:α×α, edist p.1 p.2) :=
continuous_edist.measurable

lemma measurable.edist [second_countable_topology α] [measurable_space β] {f g : β → α} :
  measurable f → measurable g → measurable (λ b, edist (f b) (g b)) :=
continuous_edist.measurable2

end emetric_space

namespace real
open measurable_space measure_theory

lemma borel_eq_generate_from_Ioo_rat :
  borel ℝ = generate_from (⋃(a b : ℚ) (h : a < b), {Ioo a b}) :=
borel_eq_generate_from_of_subbasis is_topological_basis_Ioo_rat.2.2

lemma measure_ext_Ioo_rat {μ ν : measure ℝ} [locally_finite_measure μ]
  (h : ∀ a b : ℚ, μ (Ioo a b) = ν (Ioo a b)) : μ = ν :=
begin
  refine measure.ext_of_generate_from_of_cover_subset borel_eq_generate_from_Ioo_rat _ _
    (subset.refl _) _ _ _,
  { exact countable_Union (λ a, (countable_encodable _).bUnion $ λ _ _, countable_singleton _) },
  { simp only [is_pi_system, mem_Union, mem_singleton_iff],
    rintros _ _ ⟨a₁, b₁, h₁, rfl⟩ ⟨a₂, b₂, h₂, rfl⟩ ne,
    simp only [Ioo_inter_Ioo, sup_eq_max, inf_eq_min, ← rat.cast_max, ← rat.cast_min, nonempty_Ioo] at ne ⊢,
    refine ⟨_, _, _, rfl⟩,
    assumption_mod_cast },
  { exact is_topological_basis_Ioo_rat.2.1 },
  { simp only [mem_Union, mem_singleton_iff],
    rintros _ ⟨a, b, h, rfl⟩,
    refine (measure_mono subset_closure).trans_lt _,
    rw [closure_Ioo],
    exacts [compact_Icc.finite_measure, rat.cast_lt.2 h] },
  { simp only [mem_Union, mem_singleton_iff],
    rintros _ ⟨a, b, hab, rfl⟩,
    exact h a b }
end

lemma borel_eq_generate_from_Iio_rat :
  borel ℝ = generate_from (⋃a:ℚ, {Iio a}) :=
begin
  let g, swap,
  apply le_antisymm (_ : _ ≤ g) (measurable_space.generate_from_le (λ t, _)),
  { rw borel_eq_generate_from_Ioo_rat,
    refine generate_from_le (λ t, _),
    simp only [mem_Union], rintro ⟨a, b, h, H⟩,
    rw [mem_singleton_iff.1 H],
    rw (set.ext (λ x, _) : Ioo (a:ℝ) b = (⋃c>a, (Iio c)ᶜ) ∩ Iio b),
    { have hg : ∀ q : ℚ, g.is_measurable' (Iio q) :=
        λ q, generate_measurable.basic (Iio q) (by { simp, exact ⟨_, rfl⟩ }),
      refine @is_measurable.inter _ g _ _ _ (hg _),
      refine @is_measurable.bUnion _ _ g _ _ (countable_encodable _) (λ c h, _),
      exact @is_measurable.compl _ _ g (hg _) },
    { simp [Ioo, Iio],
      refine and_congr _ iff.rfl,
      exact ⟨λ h,
        let ⟨c, ac, cx⟩ := exists_rat_btwn h in
        ⟨c, rat.cast_lt.1 ac, le_of_lt cx⟩,
       λ ⟨c, ac, cx⟩, lt_of_lt_of_le (rat.cast_lt.2 ac) cx⟩ } },
  { simp, rintro r rfl, exact is_open_Iio.is_measurable }
end

end real

lemma measurable.sub_nnreal [measurable_space α] {f g : α → nnreal} :
  measurable f → measurable g → measurable (λ a, f a - g a) :=
nnreal.continuous_sub.measurable2

lemma measurable.nnreal_of_real [measurable_space α] {f : α → ℝ} (hf : measurable f) :
  measurable (λ x, nnreal.of_real (f x)) :=
nnreal.continuous_of_real.measurable.comp hf

lemma measurable.nnreal_coe [measurable_space α] {f : α → nnreal} (hf : measurable f) :
  measurable (λ x, (f x : ℝ)) :=
nnreal.continuous_coe.measurable.comp hf

lemma measurable.ennreal_coe [measurable_space α] {f : α → nnreal} (hf : measurable f) :
  measurable (λ x, (f x : ennreal)) :=
(ennreal.continuous_coe.2 continuous_id).measurable.comp hf

lemma measurable.ennreal_of_real [measurable_space α] {f : α → ℝ} (hf : measurable f) :
  measurable (λ x, ennreal.of_real (f x)) :=
ennreal.continuous_of_real.measurable.comp hf

/-- The set of finite `ennreal` numbers is `measurable_equiv` to `nnreal`. -/
def measurable_equiv.ennreal_equiv_nnreal : measurable_equiv {r : ennreal | r ≠ ⊤} nnreal :=
ennreal.ne_top_homeomorph_nnreal.to_measurable_equiv

namespace ennreal
open filter

lemma measurable_coe : measurable (coe : nnreal → ennreal) :=
measurable_id.ennreal_coe

lemma measurable_of_measurable_nnreal [measurable_space α] {f : ennreal → α}
  (h : measurable (λp:nnreal, f p)) : measurable f :=
measurable_of_measurable_on_compl_singleton ⊤
  (measurable_equiv.ennreal_equiv_nnreal.symm.measurable_coe_iff.1 h)

/-- `ennreal` is `measurable_equiv` to `nnreal ⊕ unit`. -/
def ennreal_equiv_sum :
  measurable_equiv ennreal (nnreal ⊕ unit) :=
{ measurable_to_fun  := measurable_of_measurable_nnreal measurable_inl,
  measurable_inv_fun := measurable_sum measurable_coe (@measurable_const ennreal unit _ _ ⊤),
  .. equiv.option_equiv_sum_punit nnreal }

lemma measurable_of_measurable_nnreal_nnreal [measurable_space α] [measurable_space β]
  (f : ennreal → ennreal → β) {g : α → ennreal} {h : α → ennreal}
  (h₁ : measurable (λp:nnreal × nnreal, f p.1 p.2))
  (h₂ : measurable (λr:nnreal, f ⊤ r))
  (h₃ : measurable (λr:nnreal, f r ⊤))
  (hg : measurable g) (hh : measurable h) : measurable (λa, f (g a) (h a)) :=
let e : measurable_equiv (ennreal × ennreal)
  (((nnreal × nnreal) ⊕ (nnreal × unit)) ⊕ ((unit × nnreal) ⊕ (unit × unit))) :=
  (measurable_equiv.prod_congr ennreal_equiv_sum ennreal_equiv_sum).trans
    (measurable_equiv.sum_prod_sum _ _ _ _) in
have measurable (λp:ennreal×ennreal, f p.1 p.2),
begin
  refine e.symm.measurable_coe_iff.1 (measurable_sum (measurable_sum _ _) (measurable_sum _ _)),
  { show measurable (λp:nnreal × nnreal, f p.1 p.2),
    exact h₁ },
  { show measurable (λp:nnreal × unit, f p.1 ⊤),
    exact h₃.comp (measurable.fst measurable_id) },
  { show measurable ((λp:nnreal, f ⊤ p) ∘ (λp:unit × nnreal, p.2)),
    exact h₂.comp (measurable.snd measurable_id) },
  { show measurable (λp:unit × unit, f ⊤ ⊤),
    exact measurable_const }
end,
this.comp (measurable.prod_mk hg hh)

lemma measurable_of_real : measurable ennreal.of_real :=
ennreal.continuous_of_real.measurable

end ennreal

lemma measurable.ennreal_mul {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a * g a) :=
begin
  refine ennreal.measurable_of_measurable_nnreal_nnreal (*) _ _ _,
  { simp only [ennreal.coe_mul.symm],
    exact ennreal.measurable_coe.comp measurable_mul },
  { simp [ennreal.top_mul],
    exact measurable_const.piecewise
      (is_closed_eq continuous_id continuous_const).is_measurable
      measurable_const },
  { simp [ennreal.mul_top],
    exact measurable_const.piecewise
      (is_closed_eq continuous_id continuous_const).is_measurable
      measurable_const }
end

lemma measurable.ennreal_add {α : Type*} [measurable_space α] {f g : α → ennreal}
  (hf : measurable f) (hg : measurable g) : measurable (λa, f a + g a) :=
hf.add hg

lemma measurable.ennreal_sub {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a - g a) :=
begin
  refine ennreal.measurable_of_measurable_nnreal_nnreal (has_sub.sub) _ _ _,
  { simp only [ennreal.coe_sub.symm],
    exact ennreal.measurable_coe.comp nnreal.continuous_sub.measurable },
  { simp [measurable_const] },
  { simp [measurable_const] }
end

section normed_group

variables [measurable_space α] [normed_group α] [opens_measurable_space α] [measurable_space β]

lemma measurable_norm : measurable (norm : α → ℝ) :=
continuous_norm.measurable

lemma measurable.norm {f : β → α} (hf : measurable f) : measurable (λa, norm (f a)) :=
measurable_norm.comp hf

lemma measurable_nnnorm : measurable (nnnorm : α → nnreal) :=
continuous_nnnorm.measurable

lemma measurable.nnnorm {f : β → α} (hf : measurable f) : measurable (λa, nnnorm (f a)) :=
measurable_nnnorm.comp hf

lemma measurable.ennnorm {f : β → α} (hf : measurable f) :
  measurable (λa, (nnnorm (f a) : ennreal)) :=
hf.nnnorm.ennreal_coe

end normed_group

namespace measure_theory
namespace measure

variables [measurable_space α] [topological_space α]

/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf { μ(U) | A ⊆ U open }` for `A` measurable;
  - it is inner regular: `μ(U) = sup { μ(K) | K ⊆ U compact }` for `U` open. -/
structure regular (μ : measure α) : Prop :=
(lt_top_of_is_compact : ∀ {{K : set α}}, is_compact K → μ K < ⊤)
(outer_regular : ∀ {{A : set α}}, is_measurable A →
  (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) ≤ μ A)
(inner_regular : ∀ {{U : set α}}, is_open U →
  μ U ≤ ⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ U), μ K)

namespace regular

lemma outer_regular_eq {μ : measure α} (hμ : μ.regular) {{A : set α}}
  (hA : is_measurable A) : (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) = μ A :=
le_antisymm (hμ.outer_regular hA) $ le_infi $ λ s, le_infi $ λ hs, le_infi $ λ h2s, μ.mono h2s

lemma inner_regular_eq {μ : measure α} (hμ : μ.regular) {{U : set α}}
  (hU : is_open U) : (⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ U), μ K) = μ U :=
le_antisymm (supr_le $ λ s, supr_le $ λ hs, supr_le $ λ h2s, μ.mono h2s) (hμ.inner_regular hU)

protected lemma map [opens_measurable_space α] [measurable_space β] [topological_space β]
  [t2_space β] [borel_space β] {μ : measure α} (hμ : μ.regular) (f : α ≃ₜ β) :
  (measure.map f μ).regular :=
begin
  have hf := f.continuous.measurable,
  have h2f := f.to_equiv.injective.preimage_surjective,
  have h3f := f.to_equiv.surjective,
  split,
  { intros K hK, rw [map_apply hf hK.is_measurable],
    apply hμ.lt_top_of_is_compact, rwa f.compact_preimage },
  { intros A hA, rw [map_apply hf hA, ← hμ.outer_regular_eq (hf hA)],
    refine le_of_eq _, apply infi_congr (preimage f) h2f,
    intro U, apply infi_congr_Prop f.is_open_preimage, intro hU,
    apply infi_congr_Prop h3f.preimage_subset_preimage_iff, intro h2U,
    rw [map_apply hf hU.is_measurable], },
  { intros U hU, rw [map_apply hf hU.is_measurable, ← hμ.inner_regular_eq (f.continuous U hU)],
    refine ge_of_eq _, apply supr_congr (preimage f) h2f,
    intro K, apply supr_congr_Prop f.compact_preimage, intro hK,
    apply supr_congr_Prop h3f.preimage_subset_preimage_iff, intro h2U,
    rw [map_apply hf hK.is_measurable] }
end

protected lemma smul {μ : measure α} (hμ : μ.regular) {x : ennreal} (hx : x < ⊤) :
  (x • μ).regular :=
begin
  split,
  { intros K hK, exact ennreal.mul_lt_top hx (hμ.lt_top_of_is_compact hK) },
  { intros A hA, rw [coe_smul],
    refine le_trans _ (ennreal.mul_left_mono $ hμ.outer_regular hA),
    simp only [infi_and'], simp only [infi_subtype'],
    haveI : nonempty {s : set α // is_open s ∧ A ⊆ s} := ⟨⟨set.univ, is_open_univ, subset_univ _⟩⟩,
    rw [ennreal.mul_infi], refl', exact ne_of_lt hx },
  { intros U hU, rw [coe_smul], refine le_trans (ennreal.mul_left_mono $ hμ.inner_regular hU) _,
    simp only [supr_and'], simp only [supr_subtype'],
    rw [ennreal.mul_supr], refl' }
end

end regular

end measure
end measure_theory
