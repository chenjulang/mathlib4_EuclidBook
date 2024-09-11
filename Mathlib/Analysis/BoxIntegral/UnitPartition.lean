/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.Analysis.BoxIntegral.Partition.Tagged

/-!
# Unit Partition

Fix `n` a positive integer. `BoxIntegral.unitPartition.Box` are boxes in `ι → ℝ` obtained by
dividing the unit box uniformly into boxes of side length `1 / n` and translating the boxes by
the lattice `ι → ℤ` so that they cover the whole space. For fixed `n`, there are indexed by
vectors `ν : ι → ℤ`.

Let `B` be a `BoxIntegral`. A `unitPartition.Box` is admissible for `B` (more precisely its index is
admissible) if it is contained in `B`. There are finitely many admissible `unitPartition.Box` for
`B` and thus we can form the corresponing tagged prepartition, see
`BoxIntegral.unitPartition.prepartition` (note that each `unitPartition.Box` coming with its
tag situed at its "upper most" corner). If `B` satifies `hasIntegralVertices`, that
is its corners are in `ι → ℤ`, then the corresponding prepartition is actually a partition.

## Main definitions and results

* `BoxIntegral.hasIntegralCorners`: a `Prop` that states that the corners of the box has
coordinates in `ℤ`

* `BoxIntegral.unitPartition.box`: a `BoxIntegral`, indexed by `ν : ι → ℤ`, with corners
`ν i / n` and of side length `1 / n`.

* `BoxIntegral.unitPartition.admissibleIndex`: For `B : BoxIntegral.Box`, the set of indices of
`unitPartition.Box` that are subset of `B`. It is a finite set.

* `BoxIntegral.unitPartition.prepartition_isPartition`: For `B : BoxIntegral.Box`, if `B`
has integral corners, the prepartition of `unitPartition.Box` admissible for `B` is a partition
of `B`.
-/

noncomputable section

variable {ι : Type*}

section hasIntegralCorners

open Bornology

/-- A `BoxIntegral.Box` has integral devices if its corners has coordinates in `ℤ`. -/
def BoxIntegral.hasIntegralCorners (B : Box ι) : Prop :=
  ∃ l u : ι → ℤ, (∀ i, B.lower i = l i) ∧ (∀ i, B.upper i = u i)

/-- Any bounded set is contained in a `BoxIntegral.Box` with integral corners. -/
theorem BoxIntegral.le_hasIntegralVertices_of_isBounded [Finite ι] {s : Set (ι → ℝ)}
    (h : IsBounded s) :
    ∃ B : BoxIntegral.Box ι, hasIntegralCorners B ∧ s ≤ B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := IsBounded.subset_ball_lt h 0 0
  let C : ℕ+ := ⟨⌈R⌉₊, Nat.ceil_pos.mpr hR₁⟩
  let I : Box ι := BoxIntegral.Box.mk (fun _ ↦ - C) (fun _ ↦ C ) (fun _ ↦ by norm_num [hR₁])
  refine ⟨I, ⟨fun _ ↦ - C, fun _ ↦ C, by aesop⟩, le_trans hR₂ ?_⟩
  suffices Metric.ball (0 : ι → ℝ) C ≤ I from
    le_trans (Metric.ball_subset_ball (Nat.le_ceil R)) this
  intro x hx
  simp_rw [mem_ball_zero_iff, pi_norm_lt_iff (by aesop : (0:ℝ) < C), Real.norm_eq_abs, abs_lt] at hx
  exact fun i ↦ ⟨(hx i).1, le_of_lt (hx i).2⟩

end hasIntegralCorners

namespace BoxIntegral.unitPartition

open Bornology MeasureTheory Fintype BoxIntegral

variable (n : ℕ+)

/-- A `BoxIntegral`, indexed by a positive integer `n` and `ν : ι → ℤ`, with corners `ν i / n`
and of side length `1 / n`. -/
def box (ν : ι → ℤ) : Box ι where
  lower := fun i ↦ ν i / n
  upper := fun i ↦ ν i / n + 1 / n
  lower_lt_upper := fun _ ↦ by norm_num

@[simp]
theorem box_lower (ν : ι → ℤ) :
    (box n ν).lower = fun i ↦ (ν i / n : ℝ) := rfl

@[simp]
theorem box_upper (ν : ι → ℤ) :
    (box n ν).upper = fun i ↦ (ν i / n + 1 / n : ℝ) := rfl

variable {n} in
@[simp]
theorem mem_box_iff {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ box n ν ↔ ∀ i, ν i / n < x i ∧ x i ≤ ν i / n + 1 / n := by
  simp_rw [Box.mem_def, box, Set.mem_Ioc]

variable {n} in
theorem mem_box_iff' {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ box n ν ↔ ∀ i, ν i < n * x i ∧ n * x i ≤ ν i + 1 := by
  have h_npos : 0 < (n:ℝ) := Nat.cast_pos.mpr <| PNat.pos n
  simp_rw [mem_box_iff, ← _root_.le_div_iff₀' h_npos, ← div_lt_iff' h_npos, add_div]

/-- The tag of a `unitPartition.Box`. -/
abbrev tag (ν : ι → ℤ) : ι → ℝ := fun i ↦ (ν i + 1) / n

@[simp]
theorem tag_apply (ν : ι → ℤ) (i : ι) : tag n ν i = (ν i + 1) / n := rfl

theorem tag_injective : Function.Injective (fun ν : ι → ℤ ↦ tag n ν) := by
  refine fun _ _ h ↦ Function.funext_iff.mpr fun i ↦ ?_
  have := congr_arg (fun x ↦ x i) h
  field_simp at this
  exact this

theorem tag_mem (ν : ι → ℤ) :
    tag n ν ∈ box n ν := by
  refine mem_box_iff.mpr fun _ ↦ ?_
  rw [tag, add_div]
  exact ⟨by norm_num, le_rfl⟩

/-- For `x : ι → ℝ`, its index is the index of the unique `unitPartition.Box` to which
it belongs. -/
def index (x : ι → ℝ) (i : ι) : ℤ := ⌈n * x i⌉ - 1

@[simp]
theorem index_apply {x : ι → ℝ} (i : ι) :
    index n x i = ⌈n * x i⌉ - 1 := rfl

variable {n} in
theorem mem_box_iff_index {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ box n ν ↔ index n x = ν := by
  simp_rw [mem_box_iff', Function.funext_iff, index_apply, sub_eq_iff_eq_add, Int.ceil_eq_iff,
    Int.cast_add, Int.cast_one, add_sub_cancel_right]

@[simp]
theorem index_tag (ν : ι → ℤ) :
    index n (tag n ν) = ν := mem_box_iff_index.mp (tag_mem n ν)

variable {n} in
theorem disjoint {ν ν' : ι → ℤ} :
    ν ≠ ν' ↔ Disjoint (box n ν).toSet (box n ν').toSet := by
  rw [not_iff_not.symm, ne_eq, not_not, Set.not_disjoint_iff]
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hx'⟩ ↦ ?_⟩
  · exact ⟨tag n ν, tag_mem n ν, h ▸ tag_mem n ν⟩
  · rw [← mem_box_iff_index.mp hx, ← mem_box_iff_index.mp hx']

theorem box_injective : Function.Injective (fun ν : ι → ℤ ↦ box n ν) := by
  intro _ _ h
  contrapose! h
  exact Box.ne_of_disjoint_coe (disjoint.mp h)

variable [Fintype ι]

theorem diam_boxIcc (ν : ι → ℤ) :
    Metric.diam (Box.Icc (box n ν)) ≤ 1 / n := by
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [BoxIntegral.Box.Icc_eq_pi]
  refine EMetric.diam_pi_le_of_le (fun i ↦ ?_)
  rw [Real.ediam_Icc, box, add_sub_cancel_left, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr n.pos),
    ENNReal.ofReal_one]

@[simp]
theorem volume_box (ν : ι → ℤ) :
    volume (box n ν : Set (ι → ℝ)) = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc, box,
    add_sub_cancel_left, Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr n.pos),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast, Finset.card_univ, one_div, ENNReal.inv_pow]

theorem setFinite_index {s : Set (ι → ℝ)} (hs₁ : NullMeasurableSet s) (hs₂ : volume s ≠ ⊤) :
    Set.Finite {ν : ι → ℤ | ↑(box n ν) ⊆ s} := by
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion₀ volume (ε := 1 / n ^ card ι)
    (by norm_num) (As := fun ν : ι → ℤ ↦ (box n ν) ∩ s) (fun ν ↦ ?_) (fun _ _ h ↦ ?_) ?_).subset
      (fun _ hν ↦ ?_)
  · refine NullMeasurableSet.inter ?_ hs₁
    exact (box n ν).measurableSet_coe.nullMeasurableSet
  · exact ((Disjoint.inter_right _ (disjoint.mp h)).inter_left _ ).aedisjoint
  · exact lt_top_iff_ne_top.mp <| measure_lt_top_of_subset (by aesop) hs₂
  · rw [Set.mem_setOf, Set.inter_eq_self_of_subset_left hν, volume_box]

/-- For `B : BoxIntegral.Box`, the set of indices of `unitPartition.Box` that are subset of `B`.
It is a finite set. These boxes cover `B` if it has integral corners, see
`unitPartition.prepartition_isPartition`. -/
def admissibleIndex (B : Box ι) : Finset (ι → ℤ) := by
  refine (setFinite_index n B.measurableSet_coe.nullMeasurableSet ?_).toFinset
  exact lt_top_iff_ne_top.mp (IsBounded.measure_lt_top B.isBounded)

variable {n} in
theorem mem_admissibleIndex_iff {B : Box ι} {ν : ι → ℤ} :
    ν ∈ admissibleIndex n B ↔ box n ν ≤ B := by
  rw [admissibleIndex, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Box.coe_subset_coe]

open Classical in
/-- For `B : BoxIntegral.Box`, the `TaggedPrepartition` formed by the set of all
`unitPartition.Box` whose index is `B`-admissible. -/
def prepartition (B : Box ι) : TaggedPrepartition B where
  boxes := Finset.image (fun ν ↦ box n ν) (admissibleIndex n B)
  le_of_mem' _ hI := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hI
    exact mem_admissibleIndex_iff.mp hν
  pairwiseDisjoint _ hI₁ _ hI₂ h := by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₁
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₂
    exact disjoint.mp fun x ↦ h (congrArg (box n) x)
  tag I := by
    by_cases hI : ∃ ν ∈ admissibleIndex n B, I = box n ν
    · exact tag n hI.choose
    · exact B.exists_mem.choose
  tag_mem_Icc I := by
    by_cases hI : ∃ ν ∈ admissibleIndex n B, I = box n ν
    · simp_rw [dif_pos hI]
      exact Box.coe_subset_Icc <| (mem_admissibleIndex_iff.mp hI.choose_spec.1) (tag_mem n _)
    · simp_rw [dif_neg hI]
      exact Box.coe_subset_Icc B.exists_mem.choose_spec

variable {n} in
@[simp]
theorem mem_prepartition_iff {B I : Box ι} :
    I ∈ prepartition n B ↔ ∃ ν ∈ admissibleIndex n B, box n ν = I := by
  classical
  rw [prepartition, TaggedPrepartition.mem_mk, Prepartition.mem_mk, Finset.mem_image]

variable {n} in
theorem mem_prepartition_boxes_iff {B I : Box ι} :
    I ∈ (prepartition n B).boxes ↔ ∃ ν ∈ admissibleIndex n B, box n ν = I := by
  rw [Prepartition.mem_boxes, TaggedPrepartition.mem_toPrepartition, mem_prepartition_iff]

theorem prepartition_tag {ν : ι → ℤ} {B : Box ι} (hν : ν ∈ admissibleIndex n B) :
    (prepartition n B).tag (box n ν) = tag n ν := by
  dsimp only [prepartition]
  have h : ∃ ν' ∈ admissibleIndex n B, box n ν = box n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h, (tag_injective n).eq_iff, ← (box_injective n).eq_iff]
  exact h.choose_spec.2.symm

theorem box_index_tag_eq_self {B I : Box ι} (hI : I ∈ (prepartition n B).boxes) :
    box n (index n ((prepartition n B).tag I)) = I := by
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_boxes_iff.mp hI
  rw [prepartition_tag n hν, index_tag]

theorem prepartition_isHenstock (B : Box ι) :
    (prepartition n B).IsHenstock := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  rw [prepartition_tag n hν]
  exact Box.coe_subset_Icc (tag_mem _ _)

theorem prepartition_isSubordinate (B : Box ι) {r : ℝ} (hr : 0 < r) (hn : 1 / n ≤ r) :
    (prepartition n B).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  refine fun _ h ↦ le_trans (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) h ?_) ?_
  · rw [prepartition_tag n hν]
    exact Box.coe_subset_Icc (tag_mem _ _)
  · exact le_trans (diam_boxIcc n ν) hn

private theorem mem_admissibleIndex_of_mem_box_aux₁ (x : ℝ) (a : ℤ) :
    a < x ↔ a ≤ (⌈n * x⌉ - 1) / (n : ℝ) := by
  rw [le_div_iff₀' (by positivity), le_sub_iff_add_le, show (n : ℝ) * a + 1 =
    (n * a + 1 : ℤ) by norm_cast, Int.cast_le, Int.add_one_le_ceil_iff, Int.cast_mul,
    Int.cast_natCast, mul_lt_mul_left (by positivity)]

private theorem mem_admissibleIndex_of_mem_box_aux₂ (x : ℝ) (a : ℤ) :
    x ≤ a ↔ (⌈n * x⌉ - 1) / (n : ℝ) + 1 / n ≤ a := by
  rw [← add_div, sub_add_cancel, div_le_iff₀' (by positivity), show (n : ℝ) * a = (n * a : ℤ)
    by norm_cast, Int.cast_le, Int.ceil_le, Int.cast_mul, Int.cast_natCast, mul_le_mul_left
    (by positivity)]

/-- If `B : BoxIntegral.Box` has integral corners and contains the point `x`, then the index of
`x` is admissible for `B`. -/
theorem mem_admissibleIndex_of_mem_box {B : Box ι} (hB : hasIntegralCorners B) {x : ι → ℝ}
    (hx : x ∈ B) : index n x ∈ admissibleIndex n B := by
  obtain ⟨l, u, hl, hu⟩ := hB
  simp_rw [mem_admissibleIndex_iff, Box.le_iff_bounds, box_lower, box_upper, Pi.le_def,
    index_apply, hl, hu, ← forall_and]
  push_cast
  refine fun i ↦ ⟨?_, ?_⟩
  · exact (mem_admissibleIndex_of_mem_box_aux₁ n (x i) (l i)).mp ((hl i) ▸ (hx i).1)
  · exact (mem_admissibleIndex_of_mem_box_aux₂ n (x i) (u i)).mp ((hu i) ▸ (hx i).2)

/-- If `B : BoxIntegral.Box` has integral corners, then `prepartition n B` is a partition of
`B`. -/
theorem prepartition_isPartition {B : Box ι} (hB : hasIntegralCorners B) :
    (prepartition n B).IsPartition := by
  refine fun x hx ↦ ⟨box n (index n x), ?_, mem_box_iff_index.mpr rfl⟩
  rw [TaggedPrepartition.mem_toPrepartition, mem_prepartition_iff]
  exact ⟨index n x, mem_admissibleIndex_of_mem_box n hB hx, rfl⟩

end BoxIntegral.unitPartition
