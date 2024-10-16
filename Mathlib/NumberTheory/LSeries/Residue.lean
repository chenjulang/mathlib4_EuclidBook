/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Docstring

-/

open Filter Topology

noncomputable section

variable {a : ℕ → ℕ} {l : ℝ} (hl : 0 < l)

variable (a) in
abbrev A (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), a i

variable (hA₁ : Tendsto (fun n ↦ (∑ i ∈ Finset.range (n + 1), a i : ℝ) / n) atTop (𝓝 l))

include hl hA₁ in
theorem lemmaA1 : Tendsto (A a) atTop atTop := by
  have : Tendsto (fun n ↦ (A a n : ℝ)) atTop atTop := by
    have : Tendsto (fun n : ℕ ↦ l * (n : ℝ)) atTop atTop := by
      refine Tendsto.const_mul_atTop hl tendsto_natCast_atTop_atTop
    refine Asymptotics.IsEquivalent.tendsto_atTop ?_ this
    rw [Asymptotics.isEquivalent_comm, Asymptotics.isEquivalent_iff_tendsto_one]
    convert Tendsto.mul hA₁ (tendsto_const_nhds (x := l⁻¹))
    · simp
      ring
    · rw [mul_inv_cancel₀ hl.ne']
    · filter_upwards [eventually_ne_atTop 0] with n hn
      refine mul_ne_zero hl.ne' (Nat.cast_ne_zero.mpr hn)
  exact tendsto_natCast_atTop_iff.mp this

variable (a) in
theorem lemmaA2 : Monotone (A a) := by
  intro x y h
  rw [A, A, ← Finset.sum_range_add_sum_Ico _ ( Nat.add_le_add_right h 1)]
  exact Nat.le_add_right _ _

variable (a) in
def u (n : ℕ) : ℕ := sInf {k : ℕ | n ≤ A a k}

theorem lemma11 {n : ℕ} (hn : 0 < u a n) : A a ((u a n) - 1) < n := by
  by_contra! h
  have := csInf_le' (by exact h : (u a n) - 1 ∈ {k : ℕ | n ≤ A a k})
  exact (lt_irrefl _) <| (Nat.le_sub_one_iff_lt hn).mp this

include hl hA₁ in
theorem lemma12 (n : ℕ) : n ≤ A a (u a n) := by
  have : {k : ℕ | n ≤ A a k}.Nonempty := by
    have := tendsto_atTop_atTop.mp (lemmaA1 hl hA₁) n
    exact ⟨this.choose, this.choose_spec this.choose le_rfl⟩
  have := csInf_mem this
  exact this

include hl hA₁ in
theorem lemma_main {n : ℕ} (hn : 0 < n) : Nat.card {k | u a k = n} = a n := by
  have : {k | u a k = n} = Finset.Ioc (A a (n - 1)) (A a n) := by
    ext x
    rw [Set.mem_setOf_eq, Finset.coe_Ioc, Set.mem_Ioc]
    refine ⟨?_, ?_⟩
    · intro h
      rw [← h]
      refine ⟨lemma11 (h ▸ hn), lemma12 hl hA₁ x⟩
    · intro h
      refine IsLeast.csInf_eq ⟨?_, ?_⟩
      exact h.2
      intro y hy
      simp at hy
      have := lt_of_lt_of_le h.1 hy
      contrapose! this
      rw [Nat.lt_iff_le_pred hn] at this
      exact lemmaA2 a this
  simp_rw [this, Nat.card_eq_card_toFinset, Finset.coe_Ioc, Set.toFinset_Ioc, Nat.card_Ioc, A]
  rw [Finset.sum_range_succ, Nat.sub_one_add_one_eq_of_pos hn, Nat.add_sub_cancel_left]

include hl hA₁ in
theorem lemma20 : Monotone (u a) := by
  intro x y h
  exact le_csInf ⟨u a y, lemma12 hl hA₁ y⟩ fun _ h' ↦ csInf_le (OrderBot.bddBelow _) (h.trans h')

include hl hA₁ in
theorem lemma21 : Tendsto (u a) atTop atTop := by
  refine Monotone.tendsto_atTop_atTop (lemma20 hl hA₁) ?_
  by_contra! h
  obtain ⟨B, hB⟩ := h
  have : ∀ n, n ≤ A a B := by
    intro n
    have t₀ := lemma12 hl hA₁ n
    have t₁ := lemmaA2 a (hB n)
    have t₃ := lemmaA2 a (by exact Nat.le_add_right (u a n) 1 : u a n ≤ u a n + 1)
    exact t₀.trans (t₃.trans t₁)
  specialize this (A a B + 1)
  simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at this

include hl hA₁ in
theorem lemma3 : Tendsto (fun n : ℕ ↦ (n : ℝ) / (u a n)) atTop (𝓝 l) := by
  have h₁ : Tendsto (fun n ↦ (A a (u a n) : ℝ)/ (u a n)) atTop (𝓝 l) := by
    convert hA₁.comp (lemma21 hl hA₁)
    simp
  have h₂ : Tendsto (fun n ↦ ((A a (u a n - 1) : ℝ) / (u a n - 1 : ℕ)) * ((u a n - 1) / u a n))
      atTop (𝓝 l) := by
    have : Tendsto (fun n ↦ n - 1) atTop atTop := by exact tendsto_sub_atTop_nat 1
    have := hA₁.comp this
    have := this.comp (lemma21 hl hA₁)
    simp [Function.comp_def] at this
    rw [show 𝓝 l = 𝓝 (l * 1) by ring_nf]
    simp_rw [← Nat.cast_sum] at this
    refine Tendsto.mul this ?_
    have : Tendsto (fun n : ℕ ↦ (n - 1 : ℝ) / n) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ ↦ (n : ℝ) / (n + 1)) atTop (𝓝 1) := tendsto_natCast_div_add_atTop 1
      have := this.comp (tendsto_sub_atTop_nat 1)
      simp [Function.comp_def] at this
      refine Tendsto.congr' ?_ this
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
    have := this.comp (lemma21 hl hA₁)
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h₂ h₁ ?_ ?_
  · have := lemma21 hl hA₁
    rw [tendsto_atTop] at this
    filter_upwards [this 2] with n hn
    rw [Nat.cast_sub, Nat.cast_one, ← mul_div_assoc, div_mul_cancel₀]
    · refine div_le_div_of_nonneg_right ?_ ?_
      · rw [Nat.cast_le]
        exact (lemma11 (lt_of_lt_of_le zero_lt_two hn)).le
      · exact Nat.cast_nonneg _
    · refine sub_ne_zero_of_ne ?_
      refine LT.lt.ne' ?_
      rw [Nat.one_lt_cast]
      exact lt_of_lt_of_le one_lt_two hn
    · exact le_trans one_le_two hn
  · filter_upwards with n
    refine div_le_div_of_nonneg_right ?_ ?_
    · rw [Nat.cast_le]
      exact lemma12 hl hA₁ n
    · exact Nat.cast_nonneg _

include hl hA₁ in
theorem lemma4 {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε ≤ l) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, 0 < s → (l - ε) ^ s * (n : ℝ) ^ (- s) < u a n ^ (- s) ∧
      u a n ^ (- s) < (l + ε) ^ s * (n : ℝ) ^ (- s) := by
  rw [← sub_nonneg] at hε₂ -- To help positivity
  filter_upwards [eventually_gt_atTop 0, Metric.tendsto_nhds.mp (lemma3 hl hA₁) ε hε₁] with _ _ h
  simp_rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.inv_rpow (Nat.cast_nonneg _)]
  intro s hs
  rw [← Real.mul_rpow, ← Real.mul_rpow, Real.rpow_lt_rpow_iff, Real.rpow_lt_rpow_iff,
    mul_inv_lt_iff₀, lt_mul_inv_iff₀, ← neg_add_lt_iff_lt_add, sub_eq_add_neg,
    ← lt_neg_add_iff_add_lt (a := l), neg_add_eq_sub, ← abs_lt, mul_comm]
  exact h
  all_goals positivity

include hl hA₁ in
theorem lemma5 {s : ℝ} (hs : 1 < s) :
    Summable (fun n ↦ (u a n : ℝ) ^ (- s)) := by
  have : Summable (fun n : ℕ ↦ (l + l) ^ s * (n : ℝ) ^ (- s)) := by
    refine Summable.mul_left _ ?_
    rw [Real.summable_nat_rpow]
    exact neg_lt_neg_iff.mpr hs
  refine summable_of_isBigO this ?_
  rw [Nat.cofinite_eq_atTop]
  have := lemma4 (ε := l) hl hA₁ hl le_rfl
  refine Eventually.isBigO ?_
  filter_upwards [this] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact (hn s (lt_trans zero_lt_one hs)).2.le
  refine Real.rpow_nonneg ?_ _
  exact Nat.cast_nonneg _

include hl hA₁ in
theorem lemma6 {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε ≤ l) :
    ∃ T : Finset ℕ, ∀ s, 1 < s →
      (s - 1) * ∑ n ∈ T, (u a n : ℝ) ^ (- s) +
        (l - ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s) <
          (s - 1) * ∑' n, (u a n : ℝ) ^ (-s) ∧
      (s - 1) * ∑' n, (u a n : ℝ) ^ (-s) <
        (s - 1) * ∑ n ∈ T, (u a n : ℝ) ^ (- s) +
          (l + ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp <| lemma4 hl hA₁ hε₁ hε₂
  refine ⟨Finset.range N, fun s hs ↦ ?_⟩
  simp_rw [← sum_add_tsum_compl (s := Finset.range N) (lemma5 hl hA₁ hs), mul_add,
    add_lt_add_iff_left, mul_assoc, mul_left_comm _ (s- 1), mul_lt_mul_left (sub_pos.mpr hs),
    ← tsum_mul_left]
  have h₁ : ∀ (S : Set ℕ) (c : ℝ), Summable fun n : S ↦ c * (n : ℝ) ^ (-s) := fun S c ↦ by
    have : Summable fun n : ℕ ↦ c * (n : ℝ) ^ (- s) := by
        refine Summable.mul_left _ ?_
        rw [Real.summable_nat_rpow]
        rwa [neg_lt_neg_iff]
    exact (summable_subtype_and_compl.mpr this).1
  have h₂ : ∀ (S : Set ℕ), Summable fun n : S ↦ (u a n : ℝ) ^ (-s) :=
    fun S ↦ (summable_subtype_and_compl.mpr (lemma5 hl hA₁ hs)).1
  refine ⟨tsum_lt_tsum (i := ⟨N+1, by simp⟩) ?_ ?_ (h₁ _ ((l - ε) ^ s)) (h₂ _),
    tsum_lt_tsum (i := ⟨N+1, by simp⟩) ?_ ?_ (h₂ _) (h₁ _ ((l + ε) ^ s))⟩
  · rintro ⟨i, hi⟩
    simp only [Finset.coe_range, Set.compl_Iio, Set.mem_Ici] at hi
    exact (hN i hi s (zero_lt_one.trans hs)).1.le
  · exact (hN (N + 1) (Nat.le_add_right N 1) s (zero_lt_one.trans hs)).1
  · rintro ⟨i, hi⟩
    simp only [Finset.coe_range, Set.compl_Iio, Set.mem_Ici] at hi
    exact (hN i hi s (zero_lt_one.trans hs)).2.le
  · exact (hN (N + 1) (Nat.le_add_right N 1) s (zero_lt_one.trans hs)).2

theorem lemma7 (T : Finset ℕ) (v : ℕ → ℕ) :
    Tendsto (fun s ↦ (s - 1) * ∑ n ∈ T, (v n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 0) := by
  have h₀ : Tendsto (fun s : ℝ ↦ (s - 1) * (0 : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    refine eventuallyEq_nhdsWithin_of_eqOn ?_
    intro s hs
    dsimp only
    rw [Real.zero_rpow, mul_zero]
    have := lt_trans zero_lt_one hs
    rw [neg_ne_zero]
    exact this.ne'
  have : ∀ n ∈ T, Tendsto (fun s ↦ (s - 1) * (v n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 0) := by
    intro n _
    by_cases hv : v n = 0
    · simp_rw [hv, Nat.cast_zero]
      exact h₀
    · have : Continuous (fun s : ℝ ↦ s - 1) := by
        exact continuous_add_right (-1)
      have t₀ := this.tendsto 1
      have : Continuous (fun s : ℝ ↦ (v n : ℝ) ^ (- s)) := by
        refine Continuous.rpow ?_ ?_ ?_
        · exact continuous_const
        · exact continuous_neg
        · intro _
          left
          rw [Nat.cast_ne_zero]
          exact hv
      have t₁ := this.tendsto 1
      have := t₀.mul t₁
      convert tendsto_nhdsWithin_of_tendsto_nhds this
      rw [sub_self, zero_mul]
  have := tendsto_finset_sum _ this
  simp_rw [← Finset.mul_sum, Finset.sum_const_zero] at this
  exact this

theorem lemmaZ1 :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℝ) ^ s)
      (𝓝[>] 1) (𝓝 1) := by
  rw [← tendsto_ofReal_iff, Complex.ofReal_one]
  have : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ ↦ by aesop)
  refine Tendsto.congr' ?_ (riemannZeta_residue_one.comp this)
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  simp_rw [Function.comp_apply, zeta_eq_tsum_one_div_nat_cpow (by rwa [Complex.ofReal_re]),
    Complex.ofReal_mul, Complex.ofReal_tsum, Complex.ofReal_sub, Complex.ofReal_one, one_div,
    Complex.ofReal_inv, Complex.ofReal_cpow ( Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem lemma8 {c : ℝ} (hc : 0 < c) (T : Finset ℕ) :
    Tendsto (fun s ↦ c ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ),
      (n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 c) := by
  simp_rw [mul_assoc]
  rw [show 𝓝 c = 𝓝 (c * 1) by rw [mul_one]]
  refine Tendsto.mul ?_ ?_
  · have : Continuous fun s : ℝ ↦ c ^ s := by
      refine Continuous.rpow ?_ ?_ ?_
      · exact continuous_const
      · exact continuous_id
      · intro _
        left
        exact hc.ne'
    have := this.tendsto 1
    rw [Real.rpow_one] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · have t₀ : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), (n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 1) := by
      simp_rw [Real.rpow_neg (Nat.cast_nonneg _), ← one_div]
      exact lemmaZ1
    have t₁ : (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), (n : ℝ) ^ (- s)) =ᶠ[𝓝[>] 1]
        fun s : ℝ ↦ (s - 1) * ∑ n ∈ T, (n : ℝ) ^ (-s) +
          (s - 1) * ∑' (n : ↑(T : Set ℕ)ᶜ), (n : ℝ) ^ (-s) := by
      refine eventuallyEq_nhdsWithin_of_eqOn fun s hs ↦ ?_
      rw [← mul_add, sum_add_tsum_compl]
      rw [Real.summable_nat_rpow]
      exact neg_lt_neg_iff.mpr hs
    have t₀ := Tendsto.congr' t₁ t₀
    have t₂ := lemma7 T (fun n ↦ n)
    have := Tendsto.sub t₀ t₂
    convert this using 2
    · rw [eq_sub_iff_add_eq']
    · rw [sub_zero]

include hl hA₁ in
theorem main :
    Tendsto (fun s ↦ (s - 1) * ∑' n, (u a n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 l) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε' hε'
  let ε := min l ε'
  have h₀ : 0 < ε := by
    aesop
  have h₁ : 0 < ε / 3 := by positivity
  have h₂ : ε / 3 < l := by
    refine lt_of_lt_of_le ?_ (min_le_left l ε')
    refine div_lt_self ?_ (by norm_num)
    exact h₀
  have h₃ : 0 < l - ε / 3 := by
    exact sub_pos.mpr h₂
  have h₄ : 0 < l + ε / 3 := by
    positivity
  obtain ⟨T, hT⟩ := lemma6 hl hA₁ h₁ h₂.le
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.tendsto_nhdsWithin_nhds.mp (lemma7 T (u a)) (ε / 3) h₁
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.tendsto_nhdsWithin_nhds.mp (lemma8 h₃ T) (ε / 3) h₁
  obtain ⟨δ₃, hδ₃, hδ₃'⟩ := Metric.tendsto_nhdsWithin_nhds.mp (lemma8 h₄ T) (ε / 3) h₁
  let δ := min δ₁ (min δ₂ δ₃)
  refine ⟨δ, ?_, ?_⟩
  · simp_all only [gt_iff_lt, lt_min_iff, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, sub_pos,
    Set.mem_Ioi, dist_zero_right, norm_mul, Real.norm_eq_abs, dist_sub_eq_dist_add_right, ε, δ]
  · intro s hs hsδ
    specialize hδ₁' hs (lt_of_lt_of_le hsδ (by simp [δ]))
    specialize hδ₂' hs (lt_of_lt_of_le hsδ (by simp [δ]))
    specialize hδ₃' hs (lt_of_lt_of_le hsδ (by simp [δ]))
    simp_rw [Real.dist_eq, abs_lt] at hδ₂' hδ₃' ⊢
    rw [Real.dist_0_eq_abs, abs_lt] at hδ₁'
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_lt ?_ (sub_lt_sub_right (hT s hs).1 l)
      have := add_lt_add hδ₁'.1 hδ₂'.1
      rw [← add_sub_assoc, ← sub_add, ← sub_lt_iff_lt_add] at this
      refine le_trans ?_ this.le
      rw [sub_eq_add_neg, ← neg_div, add_thirds, neg_le_neg_iff]
      exact min_le_right l ε'
    · refine lt_of_lt_of_le (sub_lt_sub_right (hT s hs).2 l) ?_
      have := add_lt_add hδ₁'.2 hδ₃'.2
      rw [← add_sub_assoc, ← sub_sub, sub_lt_iff_lt_add] at this
      refine le_trans this.le ?_
      rw [add_thirds]
      exact min_le_right l ε'

include hl hA₁ in
theorem main₂ :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ a n) s) (𝓝[>] 1) (𝓝 l) := by
  have : ∀ (n : ℕ), {k | u a k = n}.Finite := by
    intro n
    have := lemma21 hl hA₁
    rw [← Nat.cofinite_eq_atTop, tendsto_def] at this
    have := this {n}ᶜ (by simp only [mem_cofinite, compl_compl, Set.finite_singleton])
    rwa [Set.preimage_compl, mem_cofinite, compl_compl] at this
  have t₀ := fun s (hs : s ∈ Set.Ioi (1 : ℝ)) ↦
    tsum_card_nsmul_eq_tsum this (fun n : ℕ ↦ (n : ℝ) ^ (- s)) (lemma5 hl hA₁ hs)
  simp_rw [nsmul_eq_mul] at t₀
  have t₁ := main hl hA₁
  simp_rw [LSeries, ← Complex.ofReal_natCast, LSeries.term_eq_coe, ← Complex.ofReal_tsum,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul]
  rw [Filter.tendsto_ofReal_iff]
  refine Tendsto.congr' ?_ t₁
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  simp_rw [← t₀ s hs]
  congr with n
  obtain hn | hn := Nat.eq_zero_or_pos n
  · rw [hn, Nat.cast_zero, if_pos rfl, Real.zero_rpow, mul_zero]
    rw [neg_ne_zero]
    exact (zero_lt_one.trans hs).ne'
  · rw [lemma_main hl hA₁ hn, if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
