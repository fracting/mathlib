/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import analysis.normed_space.real_inner_product
import analysis.normed_space.add_torsor
import linear_algebra.affine_space.combination

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`analysis.normed_space.real_inner_product`.  Results with longer
proofs or more geometrical content generally go in separate files.

## Main definitions

* `inner_product_geometry.angle` is the undirected angle between two
  vectors.

* `euclidean_geometry.angle`, with notation `∠`, is the undirected
  angle determined by three points.

* `euclidean_geometry.orthogonal_projection` is the orthogonal
  projection of a point onto an affine subspace.

* `euclidean_geometry.reflection` is the reflection of a point in an
  affine subspace.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use `[inner_product_space V] [metric_space P]
[normed_add_torsor V P]`.  This works better with `out_param` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

namespace inner_product_geometry
/-!
### Geometrical results on real inner product spaces

This section develops some geometrical definitions and results on real
inner product spaces, where those definitions and results can most
conveniently be developed in terms of vectors and then used to deduce
corresponding results for Euclidean affine spaces.
-/

variables {V : Type*} [inner_product_space V]

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. -/
def angle (x y : V) : ℝ := real.arccos (inner x y / (∥x∥ * ∥y∥))

/-- The cosine of the angle between two vectors. -/
lemma cos_angle (x y : V) : real.cos (angle x y) = inner x y / (∥x∥ * ∥y∥) :=
real.cos_arccos (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors does not depend on their order. -/
lemma angle_comm (x y : V) : angle x y = angle y x :=
begin
  unfold angle,
  rw [inner_comm, mul_comm]
end

/-- The angle between the negation of two vectors. -/
@[simp] lemma angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y :=
begin
  unfold angle,
  rw [inner_neg_neg, norm_neg, norm_neg]
end

/-- The angle between two vectors is nonnegative. -/
lemma angle_nonneg (x y : V) : 0 ≤ angle x y :=
real.arccos_nonneg _

/-- The angle between two vectors is at most π. -/
lemma angle_le_pi (x y : V) : angle x y ≤ π :=
real.arccos_le_pi _

/-- The angle between a vector and the negation of another vector. -/
lemma angle_neg_right (x y : V) : angle x (-y) = π - angle x y :=
begin
  unfold angle,
  rw [←real.arccos_neg, norm_neg, inner_neg_right, neg_div]
end

/-- The angle between the negation of a vector and another vector. -/
lemma angle_neg_left (x y : V) : angle (-x) y = π - angle x y :=
by rw [←angle_neg_neg, neg_neg, angle_neg_right]

/-- The angle between the zero vector and a vector. -/
@[simp] lemma angle_zero_left (x : V) : angle 0 x = π / 2 :=
begin
  unfold angle,
  rw [inner_zero_left, zero_div, real.arccos_zero]
end

/-- The angle between a vector and the zero vector. -/
@[simp] lemma angle_zero_right (x : V) : angle x 0 = π / 2 :=
begin
  unfold angle,
  rw [inner_zero_right, zero_div, real.arccos_zero]
end

/-- The angle between a nonzero vector and itself. -/
@[simp] lemma angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 :=
begin
  unfold angle,
  rw [←inner_self_eq_norm_square, div_self (λ h, hx (inner_self_eq_zero.1 h)),
      real.arccos_one]
end

/-- The angle between a nonzero vector and its negation. -/
@[simp] lemma angle_self_neg_of_nonzero {x : V} (hx : x ≠ 0) : angle x (-x) = π :=
by rw [angle_neg_right, angle_self hx, sub_zero]

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp] lemma angle_neg_self_of_nonzero {x : V} (hx : x ≠ 0) : angle (-x) x = π :=
by rw [angle_comm, angle_self_neg_of_nonzero hx]

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp] lemma angle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  angle x (r • y) = angle x y :=
begin
  unfold angle,
  rw [inner_smul_right, norm_smul, real.norm_eq_abs, abs_of_nonneg (le_of_lt hr), ←mul_assoc,
      mul_comm _ r, mul_assoc, mul_div_mul_left _ _ (ne_of_gt hr)]
end

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp] lemma angle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  angle (r • x) y = angle x y :=
by rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp] lemma angle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  angle x (r • y) = angle x (-y) :=
by rw [←neg_neg r, neg_smul, angle_neg_right, angle_smul_right_of_pos x y (neg_pos_of_neg hr),
       angle_neg_right]

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp] lemma angle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  angle (r • x) y = angle (-x) y :=
by rw [angle_comm, angle_smul_right_of_neg y x hr, angle_comm]

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma cos_angle_mul_norm_mul_norm (x y : V) : real.cos (angle x y) * (∥x∥ * ∥y∥) = inner x y :=
begin
  rw cos_angle,
  by_cases h : (∥x∥ * ∥y∥) = 0,
  { rw [h, mul_zero],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
    { rw norm_eq_zero at hx,
      rw [hx, inner_zero_left] },
    { rw norm_eq_zero at hy,
      rw [hy, inner_zero_right] } },
  { exact div_mul_cancel _ h }
end

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma sin_angle_mul_norm_mul_norm (x y : V) : real.sin (angle x y) * (∥x∥ * ∥y∥) =
    real.sqrt (inner x x * inner y y - inner x y * inner x y) :=
begin
  unfold angle,
  rw [real.sin_arccos (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                      (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2,
      ←real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
      ←real.sqrt_mul' _ (mul_self_nonneg _), pow_two,
      real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)), inner_self_eq_norm_square,
      inner_self_eq_norm_square],
  by_cases h : (∥x∥ * ∥y∥) = 0,
  { rw [(show ∥x∥ * ∥x∥ * (∥y∥ * ∥y∥) = (∥x∥ * ∥y∥) * (∥x∥ * ∥y∥), by ring), h, mul_zero, mul_zero,
        zero_sub],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
    { rw norm_eq_zero at hx,
      rw [hx, inner_zero_left, zero_mul, neg_zero] },
    { rw norm_eq_zero at hy,
      rw [hy, inner_zero_right, zero_mul, neg_zero] } },
  { field_simp [h],
    ring }
end

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
lemma angle_eq_zero_iff (x y : V) : angle x y = 0 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  unfold angle,
  rw [←inner_div_norm_mul_norm_eq_one_iff, ←real.arccos_one],
  split,
  { intro h,
    exact real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                          (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                          (by norm_num)
                          (by norm_num)
                          h },
  { intro h,
    rw h }
end

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
lemma angle_eq_pi_iff (x y : V) : angle x y = π ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  unfold angle,
  rw [←inner_div_norm_mul_norm_eq_neg_one_iff, ←real.arccos_neg_one],
  split,
  { intro h,
    exact real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                          (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                          (by norm_num)
                          (by norm_num)
                          h },
  { intro h,
    rw h }
end

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
  angle x z + angle y z = π :=
begin
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hx, ⟨r, ⟨hr, hxy⟩⟩⟩,
  rw [hxy, angle_smul_left_of_neg x z hr, angle_neg_left,
      add_sub_cancel'_right]
end

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
lemma inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : inner x y = 0 ↔ angle x y = π / 2 :=
begin
  split,
  { intro h,
    unfold angle,
    rw [h, zero_div, real.arccos_zero] },
  { intro h,
    unfold angle at h,
    rw ←real.arccos_zero at h,
    have h2 : inner x y / (∥x∥ * ∥y∥) = 0 :=
      real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                      (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                      (by norm_num)
                      (by norm_num)
                      h,
    by_cases h : (∥x∥ * ∥y∥) = 0,
    { cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
      { rw norm_eq_zero at hx,
        rw [hx, inner_zero_left] },
      { rw norm_eq_zero at hy,
        rw [hy, inner_zero_right] } },
    { simpa [h, div_eq_zero_iff] using h2 } },
end

end inner_product_geometry

namespace euclidean_geometry
/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/
open inner_product_geometry

variables {V : Type*} {P : Type*} [inner_product_space V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ p1 p2 p3`
notation. -/
def angle (p1 p2 p3 : P) : ℝ := angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

localized "notation `∠` := euclidean_geometry.angle" in euclidean_geometry

/-- The angle at a point does not depend on the order of the other two
points. -/
lemma angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
angle_comm _ _

/-- The angle at a point is nonnegative. -/
lemma angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
angle_nonneg _ _

/-- The angle at a point is at most π. -/
lemma angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
angle_le_pi _ _

/-- The angle ∠AAB at a point. -/
lemma angle_eq_left (p1 p2 : P) : ∠ p1 p1 p2 = π / 2 :=
begin
  unfold angle,
  rw vsub_self,
  exact angle_zero_left _
end

/-- The angle ∠ABB at a point. -/
lemma angle_eq_right (p1 p2 : P) : ∠ p1 p2 p2 = π / 2 :=
by rw [angle_comm, angle_eq_left]

/-- The angle ∠ABA at a point. -/
lemma angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ p1 p2 p1 = 0 :=
angle_self (λ he, h (vsub_eq_zero_iff_eq.1 he))

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
  ∠ p2 p1 p3 = 0 :=
begin
  unfold angle at h,
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩,
  unfold angle,
  rw angle_eq_zero_iff,
  rw [←neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2,
  use [hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one],
  rw [add_smul, ←neg_vsub_eq_vsub_rev p1 p2, smul_neg],
  simp [←hpr]
end

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
  ∠ p2 p3 p1 = 0 :=
begin
  rw angle_comm at h,
  exact angle_eq_zero_of_angle_eq_pi_left h
end

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
lemma angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
  ∠ p1 p2 p3 = ∠ p1 p2 p4 :=
begin
  unfold angle at h,
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hp2p3, ⟨r, ⟨hr, hpr⟩⟩⟩,
  unfold angle,
  symmetry,
  convert angle_smul_right_of_pos _ _ (add_pos (neg_pos_of_neg hr) zero_lt_one),
  rw [add_smul, ←neg_vsub_eq_vsub_rev p2 p3, smul_neg],
  simp [←hpr]
end

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
  ∠ p1 p3 p2 + ∠ p1 p3 p4 = π :=
begin
  unfold angle at h,
  rw [angle_comm p1 p3 p2, angle_comm p1 p3 p4],
  unfold angle,
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h
end

/-- The inner product of two vectors given with `weighted_vsub`, in
terms of the pairwise distances. -/
lemma inner_weighted_vsub {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P)
    (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ} (p₂ : ι₂ → P)
    (h₂ : ∑ i in s₂, w₂ i = 0) :
  inner (s₁.weighted_vsub p₁ w₁) (s₂.weighted_vsub p₂ w₂) =
    (-∑ i₁ in s₁, ∑ i₂ in s₂,
      w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) / 2 :=
begin
  rw [finset.weighted_vsub_apply, finset.weighted_vsub_apply,
      inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂],
  simp_rw [vsub_sub_vsub_cancel_right],
  rcongr i₁ i₂; rw dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)
end

/-- The distance between two points given with `affine_combination`,
in terms of the pairwise distances between the points in that
combination. -/
lemma dist_affine_combination {ι : Type*} {s : finset ι} {w₁ w₂ : ι → ℝ} (p : ι → P)
    (h₁ : ∑ i in s, w₁ i = 1) (h₂ : ∑ i in s, w₂ i = 1) :
  dist (s.affine_combination p w₁) (s.affine_combination p w₂) *
    dist (s.affine_combination p w₁) (s.affine_combination p w₂) =
    (-∑ i₁ in s, ∑ i₂ in s,
      (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 :=
begin
  rw [dist_eq_norm_vsub V (s.affine_combination p w₁) (s.affine_combination p w₂),
      ←inner_self_eq_norm_square, finset.affine_combination_vsub],
  have h : ∑ i in s, (w₁ - w₂) i = 0,
  { simp_rw [pi.sub_apply, finset.sum_sub_distrib, h₁, h₂, sub_self] },
  exact inner_weighted_vsub p h p h
end

open affine_subspace

variables {V}

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function.  This
definition is only intended for use in setting up the bundled version
`orthogonal_projection` and should not be used once that is
defined. -/
def orthogonal_projection_fn {s : affine_subspace ℝ P} (hn : (s : set P).nonempty)
    (hc : is_complete (s.direction : set V)) (p : P) : P :=
classical.some $ inter_eq_singleton_of_nonempty_of_is_compl
  hn
  (mk'_nonempty p s.direction.orthogonal)
  ((direction_mk' p s.direction.orthogonal).symm ▸ submodule.is_compl_orthogonal_of_is_complete hc)

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection_fn` of that
point onto the subspace.  This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
lemma inter_eq_singleton_orthogonal_projection_fn {s : affine_subspace ℝ P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) (p : P) :
  (s : set P) ∩ (mk' p s.direction.orthogonal) = {orthogonal_projection_fn hn hc p} :=
classical.some_spec $ inter_eq_singleton_of_nonempty_of_is_compl
  hn
  (mk'_nonempty p s.direction.orthogonal)
  ((direction_mk' p s.direction.orthogonal).symm ▸ submodule.is_compl_orthogonal_of_is_complete hc)

/-- The `orthogonal_projection_fn` lies in the given subspace.  This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem {s : affine_subspace ℝ P} (hn : (s : set P).nonempty)
    (hc : is_complete (s.direction : set V)) (p : P) : orthogonal_projection_fn hn hc p ∈ s :=
begin
  rw [←mem_coe, ←set.singleton_subset_iff, ←inter_eq_singleton_orthogonal_projection_fn],
  exact set.inter_subset_left _ _
end

/-- The `orthogonal_projection_fn` lies in the orthogonal
subspace.  This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem_orthogonal {s : affine_subspace ℝ P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) (p : P) :
  orthogonal_projection_fn hn hc p ∈ mk' p s.direction.orthogonal :=
begin
  rw [←mem_coe, ←set.singleton_subset_iff, ←inter_eq_singleton_orthogonal_projection_fn],
  exact set.inter_subset_right _ _
end

/-- Subtracting `p` from its `orthogonal_projection_fn` produces a
result in the orthogonal direction.  This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
lemma orthogonal_projection_fn_vsub_mem_direction_orthogonal {s : affine_subspace ℝ P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) (p : P) :
  orthogonal_projection_fn hn hc p -ᵥ p ∈ s.direction.orthogonal :=
direction_mk' p s.direction.orthogonal ▸
  vsub_mem_direction (orthogonal_projection_fn_mem_orthogonal hn hc p) (self_mem_mk' _ _)

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonal_projection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. For most purposes,
`orthogonal_projection`, which removes the `nonempty` and
`is_complete` hypotheses and is the identity map when either of those
hypotheses fails, should be used instead. -/
def orthogonal_projection_of_nonempty_of_complete {s : affine_subspace ℝ P}
  (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) : affine_map ℝ P P :=
{ to_fun := orthogonal_projection_fn hn hc,
  linear := orthogonal_projection s.direction,
  map_vadd' := λ p v, begin
    have hs : (orthogonal_projection s.direction) v +ᵥ orthogonal_projection_fn hn hc p ∈ s :=
      vadd_mem_of_mem_direction (orthogonal_projection_mem hc _)
                                (orthogonal_projection_fn_mem hn hc p),
    have ho : (orthogonal_projection s.direction) v +ᵥ orthogonal_projection_fn hn hc p ∈
      mk' (v +ᵥ p) s.direction.orthogonal,
    { rw [←vsub_right_mem_direction_iff_mem (self_mem_mk' _ _) _, direction_mk',
          vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc],
      refine submodule.add_mem _ (orthogonal_projection_fn_vsub_mem_direction_orthogonal hn hc p) _,
      rw submodule.mem_orthogonal',
      intros w hw,
      rw [←neg_sub, inner_neg_left, orthogonal_projection_inner_eq_zero _ _ w hw, neg_zero] },
    have hm : (orthogonal_projection s.direction) v +ᵥ orthogonal_projection_fn hn hc p ∈
      ({orthogonal_projection_fn hn hc (v +ᵥ p)} : set P),
    { rw ←inter_eq_singleton_orthogonal_projection_fn hn hc (v +ᵥ p),
      exact set.mem_inter hs ho },
    rw set.mem_singleton_iff at hm,
    exact hm.symm
  end }

/-- The orthogonal projection of a point onto an affine subspace,
which is expected to be nonempty and complete.  The corresponding
linear map (mapping a vector to the difference between the projections
of two points whose difference is that vector) is the
`orthogonal_projection` for real inner product spaces, onto the
direction of the affine subspace being projected onto.  If the
subspace is empty or not complete, this uses the identity map
instead. -/
def orthogonal_projection (s : affine_subspace ℝ P) : affine_map ℝ P P :=
if h : (s : set P).nonempty ∧ is_complete (s.direction : set V) then
  orthogonal_projection_of_nonempty_of_complete h.1 h.2 else affine_map.id ℝ P

/-- The definition of `orthogonal_projection` using `if`. -/
lemma orthogonal_projection_def (s : affine_subspace ℝ P) :
  orthogonal_projection s = if h : (s : set P).nonempty ∧ is_complete (s.direction : set V) then
    orthogonal_projection_of_nonempty_of_complete h.1 h.2 else affine_map.id ℝ P :=
rfl

@[simp] lemma orthogonal_projection_fn_eq {s : affine_subspace ℝ P} (hn : (s : set P).nonempty)
  (hc : is_complete (s.direction : set V)) (p : P) :
  orthogonal_projection_fn hn hc p = orthogonal_projection s p :=
by { rw [orthogonal_projection_def, dif_pos (and.intro hn hc)], refl }

/-- The linear map corresponding to `orthogonal_projection`. -/
@[simp] lemma orthogonal_projection_linear {s : affine_subspace ℝ P} (hn : (s : set P).nonempty) :
  (orthogonal_projection s).linear = _root_.orthogonal_projection s.direction :=
begin
  by_cases hc : is_complete (s.direction : set V),
  { rw [orthogonal_projection_def, dif_pos (and.intro hn hc)],
    refl },
  { simp [orthogonal_projection_def, _root_.orthogonal_projection_def, hn, hc] }
end

@[simp] lemma orthogonal_projection_of_nonempty_of_complete_eq {s : affine_subspace ℝ P}
  (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) (p : P) :
  orthogonal_projection_of_nonempty_of_complete hn hc p = orthogonal_projection s p :=
by rw [orthogonal_projection_def, dif_pos (and.intro hn hc)]

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection` of that point
onto the subspace. -/
lemma inter_eq_singleton_orthogonal_projection {s : affine_subspace ℝ P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) (p : P) :
  (s : set P) ∩ (mk' p s.direction.orthogonal) = {orthogonal_projection s p} :=
begin
  rw ←orthogonal_projection_fn_eq hn hc,
  exact inter_eq_singleton_orthogonal_projection_fn hn hc p
end

/-- The `orthogonal_projection` lies in the given subspace. -/
lemma orthogonal_projection_mem {s : affine_subspace ℝ P} (hn : (s : set P).nonempty)
    (hc : is_complete (s.direction : set V)) (p : P) : orthogonal_projection s p ∈ s :=
begin
  rw ←orthogonal_projection_fn_eq hn hc,
  exact orthogonal_projection_fn_mem hn hc p
end

/-- The `orthogonal_projection` lies in the orthogonal subspace. -/
lemma orthogonal_projection_mem_orthogonal (s : affine_subspace ℝ P) (p : P) :
  orthogonal_projection s p ∈ mk' p s.direction.orthogonal :=
begin
  rw orthogonal_projection_def,
  split_ifs,
  { exact orthogonal_projection_fn_mem_orthogonal h.1 h.2 p },
  { exact self_mem_mk' _ _ }
end

/-- Subtracting a point in the given subspace from the
`orthogonal_projection` produces a result in the direction of the
given subspace. -/
lemma orthogonal_projection_vsub_mem_direction {s : affine_subspace ℝ P}
    (hc : is_complete (s.direction : set V)) {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
  orthogonal_projection s p2 -ᵥ p1 ∈ s.direction :=
vsub_mem_direction (orthogonal_projection_mem ⟨p1, hp1⟩ hc p2) hp1

/-- Subtracting the `orthogonal_projection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
lemma vsub_orthogonal_projection_mem_direction {s : affine_subspace ℝ P}
    (hc : is_complete (s.direction : set V)) {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
  p1 -ᵥ orthogonal_projection s p2 ∈ s.direction :=
vsub_mem_direction hp1 (orthogonal_projection_mem ⟨p1, hp1⟩ hc p2)

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
lemma orthogonal_projection_eq_self_iff {s : affine_subspace ℝ P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) {p : P} :
  orthogonal_projection s p = p ↔ p ∈ s :=
begin
  split,
  { exact λ h, h ▸ orthogonal_projection_mem hn hc p },
  { intro h,
    have hp : p ∈ ((s : set P) ∩ mk' p s.direction.orthogonal) := ⟨h, self_mem_mk' p _⟩,
    rw [inter_eq_singleton_orthogonal_projection hn hc p, set.mem_singleton_iff] at hp,
    exact hp.symm }
end

/-- Orthogonal projection is idempotent. -/
@[simp] lemma orthogonal_projection_orthogonal_projection (s : affine_subspace ℝ P) (p : P) :
  orthogonal_projection s (orthogonal_projection s p) = orthogonal_projection s p :=
begin
  by_cases h : (s : set P).nonempty ∧ is_complete (s.direction : set V),
  { rw orthogonal_projection_eq_self_iff h.1 h.2,
    exact orthogonal_projection_mem h.1 h.2 p },
  { simp [orthogonal_projection_def, h] }
end

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
lemma dist_orthogonal_projection_eq_zero_iff {s : affine_subspace ℝ P}
  (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) {p : P} :
  dist p (orthogonal_projection s p) = 0 ↔ p ∈ s :=
by rw [dist_comm, dist_eq_zero, orthogonal_projection_eq_self_iff hn hc]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
lemma dist_orthogonal_projection_ne_zero_of_not_mem {s : affine_subspace ℝ P}
    (hn : (s : set P).nonempty) (hc : is_complete (s.direction : set V)) {p : P} (hp : p ∉ s) :
  dist p (orthogonal_projection s p) ≠ 0 :=
mt (dist_orthogonal_projection_eq_zero_iff hn hc).mp hp

/-- Subtracting `p` from its `orthogonal_projection` produces a result
in the orthogonal direction. -/
lemma orthogonal_projection_vsub_mem_direction_orthogonal (s : affine_subspace ℝ P) (p : P) :
  orthogonal_projection s p -ᵥ p ∈ s.direction.orthogonal :=
begin
  rw orthogonal_projection_def,
  split_ifs,
  { exact orthogonal_projection_fn_vsub_mem_direction_orthogonal h.1 h.2 p },
  { simp }
end

/-- Subtracting the `orthogonal_projection` from `p` produces a result
in the orthogonal direction. -/
lemma vsub_orthogonal_projection_mem_direction_orthogonal (s : affine_subspace ℝ P) (p : P) :
  p -ᵥ orthogonal_projection s p ∈ s.direction.orthogonal :=
direction_mk' p s.direction.orthogonal ▸
  vsub_mem_direction (self_mem_mk' _ _) (orthogonal_projection_mem_orthogonal s p)

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
lemma orthogonal_projection_vadd_eq_self {s : affine_subspace ℝ P}
    (hc : is_complete (s.direction : set V)) {p : P} (hp : p ∈ s) {v : V}
    (hv : v ∈ s.direction.orthogonal) : orthogonal_projection s (v +ᵥ p) = p :=
begin
  have h := vsub_orthogonal_projection_mem_direction_orthogonal s (v +ᵥ p),
  rw [vadd_vsub_assoc, submodule.add_mem_iff_right _ hv] at h,
  refine (eq_of_vsub_eq_zero _).symm,
  refine submodule.disjoint_def.1 s.direction.orthogonal_disjoint _ _ h,
  exact vsub_mem_direction hp (orthogonal_projection_mem ⟨p, hp⟩ hc (v +ᵥ p))
end

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
lemma orthogonal_projection_vadd_smul_vsub_orthogonal_projection {s : affine_subspace ℝ P}
    (hc : is_complete (s.direction : set V)) {p1 : P} (p2 : P) (r : ℝ) (hp : p1 ∈ s) :
  orthogonal_projection s (r • (p2 -ᵥ orthogonal_projection s p2 : V) +ᵥ p1) = p1 :=
orthogonal_projection_vadd_eq_self hc hp
  (submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

/-- The square of the distance from a point in `s` to `p2` equals the
sum of the squares of the distances of the two points to the
`orthogonal_projection`. -/
lemma dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
    {s : affine_subspace ℝ P} {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
  dist p1 p2 * dist p1 p2 =
    dist p1 (orthogonal_projection s p2) * dist p1 (orthogonal_projection s p2) +
    dist p2 (orthogonal_projection s p2) * dist p2 (orthogonal_projection s p2) :=
begin
  rw [metric_space.dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _,
    dist_eq_norm_vsub V _ p2, ← vsub_add_vsub_cancel p1 (orthogonal_projection s p2) p2,
    norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero],
  rw orthogonal_projection_def,
  split_ifs,
  { rw orthogonal_projection_of_nonempty_of_complete_eq,
    exact submodule.inner_right_of_mem_orthogonal
     (vsub_orthogonal_projection_mem_direction h.2 p2 hp1)
     (orthogonal_projection_vsub_mem_direction_orthogonal s p2) },
  { simp }
end

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
lemma dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd {s : affine_subspace ℝ P}
    {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (r1 r2 : ℝ) {v : V}
    (hv : v ∈ s.direction.orthogonal) :
  dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
    dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (∥v∥ * ∥v∥) :=
calc dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2)
    = ∥(p1 -ᵥ p2) + (r1 - r2) • v∥ * ∥(p1 -ᵥ p2) + (r1 - r2) • v∥
  : by { rw [dist_eq_norm_vsub V (r1 • v +ᵥ p1), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul],
         abel }
... = ∥p1 -ᵥ p2∥ * ∥p1 -ᵥ p2∥ + ∥(r1 - r2) • v∥ * ∥(r1 - r2) • v∥
  : norm_add_square_eq_norm_square_add_norm_square
      (submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp1 hp2)
        (submodule.smul_mem _ _ hv))
... = ∥(p1 -ᵥ p2 : V)∥ * ∥(p1 -ᵥ p2 : V)∥ + abs (r1 - r2) * abs (r1 - r2) * ∥v∥ * ∥v∥
  : by { rw [norm_smul, real.norm_eq_abs], ring }
... = dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (∥v∥ * ∥v∥)
  : by { rw [dist_eq_norm_vsub V p1, abs_mul_abs_self, mul_assoc] }

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete.  The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases.  If
the subspace is empty or not complete, `orthogonal_projection` is
defined as the identity map, which results in `reflection` being the
identity map in that case as well. -/
def reflection (s : affine_subspace ℝ P) : P ≃ᵢ P :=
{ to_fun := λ p, (orthogonal_projection s p -ᵥ p) +ᵥ orthogonal_projection s p,
  inv_fun := λ p, (orthogonal_projection s p -ᵥ p) +ᵥ orthogonal_projection s p,
  left_inv := λ p, by simp [vsub_vadd_eq_vsub_sub, -orthogonal_projection_linear],
  right_inv := λ p, by simp [vsub_vadd_eq_vsub_sub, -orthogonal_projection_linear],
  isometry_to_fun := begin
    dsimp only,
    rw isometry_emetric_iff_metric,
    intros p₁ p₂,
    rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_eq_norm_vsub V
          ((orthogonal_projection s p₁ -ᵥ p₁) +ᵥ orthogonal_projection s p₁),
        dist_eq_norm_vsub V p₁, ←inner_self_eq_norm_square, ←inner_self_eq_norm_square],
    by_cases h : (s : set P).nonempty ∧ is_complete (s.direction : set V),
    { calc inner
        (orthogonal_projection s p₁ -ᵥ p₁ +ᵥ orthogonal_projection s p₁ -ᵥ
         (orthogonal_projection s p₂ -ᵥ p₂ +ᵥ orthogonal_projection s p₂))
        (orthogonal_projection s p₁ -ᵥ p₁ +ᵥ orthogonal_projection s p₁ -ᵥ
         (orthogonal_projection s p₂ -ᵥ p₂ +ᵥ orthogonal_projection s p₂))
      = inner
        ((_root_.orthogonal_projection s.direction (p₁ -ᵥ p₂)) +
          _root_.orthogonal_projection s.direction (p₁ -ᵥ p₂) -
          (p₁ -ᵥ p₂))
         (_root_.orthogonal_projection s.direction (p₁ -ᵥ p₂) +
          _root_.orthogonal_projection s.direction (p₁ -ᵥ p₂) -
          (p₁ -ᵥ p₂))
    : by rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
             ←vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub, ←add_sub_assoc,
             ←affine_map.linear_map_vsub, orthogonal_projection_linear h.1]
  ... = -4 * inner (p₁ -ᵥ p₂ - (_root_.orthogonal_projection s.direction (p₁ -ᵥ p₂)))
                   (_root_.orthogonal_projection s.direction (p₁ -ᵥ p₂)) +
          inner (p₁ -ᵥ p₂) (p₁ -ᵥ p₂)
    : by { simp [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
                 inner_comm (p₁ -ᵥ p₂)],
           ring }
  ... = -4 * 0 + inner (p₁ -ᵥ p₂) (p₁ -ᵥ p₂)
    : by rw orthogonal_projection_inner_eq_zero s.direction _ _ (_root_.orthogonal_projection_mem h.2 _)
  ... = inner (p₁ -ᵥ p₂) (p₁ -ᵥ p₂) : by simp },
    { simp [orthogonal_projection_def, h] }
  end }

/-- The result of reflecting. -/
lemma reflection_apply (s : affine_subspace ℝ P) (p : P) :
  reflection s p = (orthogonal_projection s p -ᵥ p) +ᵥ orthogonal_projection s p :=
rfl

/-- Reflection is its own inverse. -/
@[simp] lemma reflection_symm (s : affine_subspace ℝ P) : (reflection s).symm = reflection s :=
rfl

/-- Reflecting twice in the same subspace. -/
@[simp] lemma reflection_reflection (s : affine_subspace ℝ P) (p : P) :
  reflection s (reflection s p) = p :=
(reflection s).left_inv p

/-- Reflection is involutive. -/
lemma reflection_involutive (s : affine_subspace ℝ P) : function.involutive (reflection s) :=
reflection_reflection s

/-- A point is its own reflection if and only if it is in the
subspace. -/
lemma reflection_eq_self_iff {s : affine_subspace ℝ P} (hn : (s : set P).nonempty)
  (hc : is_complete (s.direction : set V)) (p : P) : reflection s p = p ↔ p ∈ s :=
begin
  rw [←orthogonal_projection_eq_self_iff hn hc, reflection_apply],
  split,
  { intro h,
    rw [←@vsub_eq_zero_iff_eq V, vadd_vsub_assoc,
        ←two_smul ℝ (orthogonal_projection s p -ᵥ p), smul_eq_zero] at h,
    norm_num at h,
    exact h },
  { intro h,
    simp [h] }
end

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
lemma reflection_eq_iff_orthogonal_projection_eq (s₁ s₂ : affine_subspace ℝ P) (p : P) :
  reflection s₁ p = reflection s₂ p ↔
    orthogonal_projection s₁ p = orthogonal_projection s₂ p :=
begin
  rw [reflection_apply, reflection_apply],
  split,
  { intro h,
    rw [←@vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm,
        add_sub_assoc, vsub_sub_vsub_cancel_right,
        ←two_smul ℝ (orthogonal_projection s₁ p -ᵥ orthogonal_projection s₂ p),
        smul_eq_zero] at h,
    norm_num at h,
    exact h },
  { intro h,
    rw h }
end

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
lemma dist_reflection (s : affine_subspace ℝ P) (p₁ p₂ : P) :
  dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ :=
begin
  conv_lhs { rw ←reflection_reflection s p₁ },
  exact (reflection s).dist_eq _ _
end

/-- A point in the subspace is equidistant from another point and its
reflection. -/
lemma dist_reflection_eq_of_mem (s : affine_subspace ℝ P) {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
  dist p₁ (reflection s p₂) = dist p₁ p₂ :=
begin
  by_cases h : (s : set P).nonempty ∧ is_complete (s.direction : set V),
  { rw ←reflection_eq_self_iff h.1 h.2 p₁ at hp₁,
    conv_lhs { rw ←hp₁ },
    exact (reflection s).dist_eq _ _ },
  { simp [reflection_apply, orthogonal_projection_def, h] }
end

end euclidean_geometry
