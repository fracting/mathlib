
import testing.slim_check.sampleable
import data.finmap
import data.multiset.sort

universes u v w

inductive total_function.default (α : Type u) : Type u → Type (u+1)
| value {β} : β → total_function.default β
| self : total_function.default α

inductive total_function (α : Type u) : Type u → Type (u+1)
| with_default {β} : finmap (λ _ : α, β) → β → total_function β
| map_to_self : finmap (λ _ : α, α) → total_function α

namespace slim_check

namespace total_function
open sampleable_ext

def apply {α : Type u} [decidable_eq α] : Π {β : Type u}, total_function α β → α → β
| β (total_function.with_default m y) x := (m.lookup x).get_or_else y
| β (total_function.map_to_self m) x := (m.lookup x).get_or_else x

def finmap.map {α α'} [decidable_eq α'] {β : α → Type v} {β' : α' → Type w} (f : sigma β → sigma β') (m : finmap β) : finmap β' :=
finmap.lift_on m (λ x, (x.entries.map $ f).to_alist.to_finmap) (λ a b h, sorry)

def total_function.map {α : Type u} [decidable_eq α] : Π {β : Type u}, total_function α β → α → β
| β (total_function.with_default m x) y := (m.lookup y).get_or_else x
| β (total_function.map_to_self m) y := (m.lookup y).get_or_else y

#check @total_function.map

def repr_aux {α : Type u} [has_repr α] {β : Type u} [has_repr β] (m : finmap (λ _ : α, β)) : string :=
string.join $ multiset.sort (≤) (m.entries.map $ λ x, sformat!"{repr $ sigma.fst x} ↦ {repr $ sigma.snd x}, ")

protected def repr {α : Type u} [has_repr α] : Π {β : Type u} [has_repr β], total_function α β → string
| β Iβ (total_function.with_default m y) := sformat!"[{@repr_aux _ _ _ Iβ m}_ ↦ {@has_repr.repr _ Iβ y}]"
| _ _ (total_function.map_to_self m) := sformat!"[{repr_aux m}x ↦ x]"

instance (α : Type u) (β : Type u) [has_repr α] [has_repr β] : has_repr (total_function α β) :=
⟨ total_function.repr ⟩

@[simp]
def prod.to_sigma {α β} : α × β → Σ _ : α, β
| ⟨x,y⟩ := ⟨x,y⟩

@[simp]
lemma prod.fst_to_sigma {α β} (x : α × β) : (prod.to_sigma x).fst = x.fst :=
by cases x; refl

@[reducible]
protected def proxy_repr (α : Type u) (β : Type v) [sampleable α] [sampleable β] :=
total_function (ulift.{max u v} α) (ulift.{max v u} β)

protected def interp (α : Type u) (β : Type v) [sampleable α] [decidable_eq α] [sampleable β] (m : total_function.proxy_repr α β) (x : α) : β :=
ulift.down $ total_function.apply m (ulift.up x)

-- (@sampleable_ext.interp α _ ∘ ulift.down : ulift.{max u v} (proxy_repr α) → α) (@sampleable_ext.interp β _ ∘ ulift.down : ulift.{max v u} (proxy_repr β) → β)

instance ulift.has_repr {α} [has_repr α] : has_repr (ulift α) :=
⟨ λ ⟨x⟩, repr x ⟩

instance pi.sampleable_ext {α : Type u} {β : Type v} [has_repr α] [has_repr β] [sampleable α] [decidable_eq α] [sampleable β] : sampleable_ext (α → β) :=
{ proxy_repr := total_function (ulift.{max u v} α) (ulift.{max v u} β),
  interp := total_function.interp α β,
  sample := do {
    ⟨xs⟩ ← (uliftable.up $ sampleable.sample (list (α × β)) : gen (ulift.{(max u v)+1} (list (α × β)))),
    ⟨x⟩ ← (uliftable.up $ sample β : gen (ulift.{(max u v)+1} β)),
    pure $ total_function.with_default (xs.map $ prod.to_sigma ∘ prod.map ulift.up ulift.up).to_finmap ⟨x⟩ },
  shrink := λ _, lazy_list.nil }

@[priority 2000]
instance pi_pred.sampleable_ext {α : Type u} [sampleable_ext (α → bool)] : sampleable_ext.{u+1} (α → Prop) :=
{ proxy_repr := proxy_repr (α → bool),
  interp := λ m x, interp (α → bool) m x,
  sample := sample (α → bool),
  shrink := shrink }

@[priority 2000]
instance pi_uncurry.sampleable_ext {α : Type u} {β : Type v} {γ : Sort w} [sampleable_ext (α × β → γ)] : sampleable_ext.{(imax (u+1) (v+1) w)} (α → β → γ) :=
{ proxy_repr := proxy_repr (α × β → γ),
  interp := λ m x y, interp (α × β → γ) m (x, y),
  sample := sample (α × β → γ),
  shrink := shrink }


section

-- set_option trace.class_instances true

example : sampleable_ext (ℤ → ℤ → Prop) := by apply_instance

end
#sample (ℤ → ℤ → Prop)


section tactic
setup_tactic_parser

@[interactive]
meta def swap_names (ls : parse $ list_of (prod.mk <$> ident <*> ident)) : tactic unit :=
tactic.rename_many (native.rb_map.of_list $ ls ++ ls.map prod.swap) ff

end tactic

lemma lookup_zip_self_or_else {α} [decidable_eq α] (x : α) (xs : list α) :
  (list.lookup x $ list.map prod.to_sigma $ xs.zip xs).get_or_else x = x :=
begin
  induction xs; simp [option.get_or_else, list.lookup],
  split_ifs,
  { rw h, refl },
  assumption
end

def list.apply_id {α : Type u} [decidable_eq α] (x : α) (xs : list (α × α)) : α :=
((xs.map prod.to_sigma).lookup x).get_or_else x

@[simp]
lemma list.apply_id_cons {α : Type u} [decidable_eq α] (x a b : α) (xs : list (α × α)) :
  list.apply_id x ((a, b) :: xs) = if a = x then b else list.apply_id x xs :=
by simp [list.apply_id, list.lookup]; split_ifs; refl

example {α} [sampleable α] [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs) (h₁ : xs ~ ys) : function.injective
    (total_function.apply
       (total_function.map_to_self (list.map (prod.to_sigma) (xs.zip ys)).to_finmap))
:=
begin
  intros a b h',
  simp [total_function.interp, apply] at h',
  -- rw [← list.apply_id, ← list.apply_id] at h',
  induction h₁,
  case list.perm.nil
  { simpa [option.get_or_else], },
  case list.perm.cons
  { simp [option.get_or_else, prod.to_sigma, list.lookup] at h',
    split_ifs at h'; subst_vars; [skip, swap_names [a b], skip],
    -- { cases h₀,
    -- solve_by_elim },
    -- iterate 2
    { cases hb : (list.lookup b (list.map prod.to_sigma (h₁_l₁.zip h₁_l₂))),
      { simp [hb] at h', assumption },
      -- rw ← hb,
      -- cases h_1, refl,
      -- cases h₀,

      -- rw [list.lookup_is_some] at hb,

-- intro h, specialize h₀_a_1 _ _ h,
      apply h₁_ih, cases h₀, assumption,
      rw [hb],
      dsimp [option.get_or_else] at h' ⊢,
      -- cases h_val : list.lookup h₁_x (list.map prod.to_sigma (h₁_l₁.zip h₁_l₂)),
      -- { dsimp [option.get_or_else], rw h_val, },
      rw hb at h', cases h',

      rw [h'] <|> rw [← h'],
      rw [list.lookup_eq_none.2], refl,
      rw [show (list.map prod.to_sigma (h₁_l₁.zip h₁_l₂)).keys = h₁_l₁, from _],
      cases h₀, intro h, apply h₀_a_1 _ h rfl,
      simp [list.keys, prod.to_sigma, (∘)],
      rw list.map_fst_zip,
      solve_by_elim [le_of_eq, list.perm.length_eq], },
    cases h₀,
    solve_by_elim },
  case list.perm.swap
  { simp [option.get_or_else, prod.to_sigma, list.lookup, list.lookup] at h',
    split_ifs at h'; subst_vars,
    { cases h', refl },
    all_goals {
      simp [option.get_or_else, lookup_zip_self_or_else] at h', subst_vars,
      assumption <|> contradiction <|> skip, }, },

  cases ha : list.lookup a (list.map prod.to_sigma (xs.zip ys));
  cases hb : list.lookup b (list.map prod.to_sigma (xs.zip ys));
  simp [ha, hb, option.get_or_else] at h',
  { assumption },
  { simp [list.lookmap_map_eq] at hb }
end
-- #check list.lookup_
instance pi_injective.sampleable_ext {α : Type u} [has_repr α] [sampleable α] [decidable_eq α] : sampleable_ext { f : α → α // function.injective f } :=
{ proxy_repr := { f : total_function (ulift.{u} α) (ulift.{u} α) // function.injective (total_function.interp α α f) },
  interp := subtype.map (total_function.interp α α) $ λ x h, h,
  sample := do {
    ⟨xs⟩ ← (uliftable.up $ sampleable.sample (list α) : gen (ulift.{u+1} (list α))),
    ⟨⟨ys,h⟩⟩ ← (uliftable.up $ gen.permutation_of xs : gen (ulift.{u+1} _)),
    pure $ ⟨total_function.map_to_self ((xs.zip ys).map $ prod.to_sigma ∘ prod.map ulift.up ulift.up).to_finmap, _⟩ },
  shrink := λ _, lazy_list.nil }


end total_function

end slim_check
