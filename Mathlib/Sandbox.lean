import Mathlib

open Filter Topology

noncomputable section

variable {a : ℕ → ℕ} {l : ℝ} (hl : 0 < l)

variable (a) in
def A (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), a i

variable (hA₁ : Tendsto (fun x ↦ (A a x : ℝ) / x) atTop (𝓝 l))

include hl hA₁ in
theorem lemmaA1 : Tendsto (A a) atTop atTop := by
  have : Tendsto (fun n ↦ (A a n : ℝ)) atTop atTop := by
    have : Tendsto (fun n : ℕ ↦ l * (n : ℝ)) atTop atTop := by
      refine Tendsto.const_mul_atTop hl tendsto_natCast_atTop_atTop
    refine Asymptotics.IsEquivalent.tendsto_atTop ?_ this
    rw [Asymptotics.isEquivalent_comm, Asymptotics.isEquivalent_iff_tendsto_one]
    convert Tendsto.mul hA₁ (tendsto_const_nhds (x := l⁻¹))
    · dsimp
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
  have h₁ : Tendsto (fun n ↦ (A a (u a n) : ℝ)/ (u a n)) atTop (𝓝 l) := hA₁.comp (lemma21 hl hA₁)
  have h₂ : Tendsto (fun n ↦ ((A a (u a n - 1) : ℝ) / (u a n - 1 : ℕ)) * ((u a n - 1) / u a n))
      atTop (𝓝 l) := by
    have : Tendsto (fun n ↦ n - 1) atTop atTop := by exact tendsto_sub_atTop_nat 1
    have := hA₁.comp this
    have := this.comp (lemma21 hl hA₁)
    simp [Function.comp_def] at this
    rw [show 𝓝 l = 𝓝 (l * 1) by ring_nf]
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
theorem lemma4 {ε s : ℝ} (hε₁ : 0 < ε) (hε₂ : ε ≤ l) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, (l - ε) ^ s * (n : ℝ) ^ (- s) < u a n ^ (- s) ∧
      u a n ^ (- s) < (l + ε) ^ s * (n : ℝ) ^ (- s) := by
  rw [← sub_nonneg] at hε₂ -- To help positivity
  filter_upwards [eventually_gt_atTop 0, Metric.tendsto_nhds.mp (lemma3 hl hA₁) ε hε₁] with _ _ h
  simp_rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.inv_rpow (Nat.cast_nonneg _)]
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
  have := lemma4 (ε := l) (s := s) hl hA₁ hl le_rfl (zero_lt_one.trans hs)
  refine Eventually.isBigO ?_
  filter_upwards [this] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact hn.2.le
  refine Real.rpow_nonneg ?_ _
  exact Nat.cast_nonneg _

theorem lemma6 {ε s : ℝ} (hε₁ : 0 < ε) (hε₂ : ε ≤ l) (hs : 1 < s) :
  ∃ T : Finset ℕ,
    (l - ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s) +
      (s - 1) * ∑' n : T, (u a n : ℝ) ^ (- s) ≤
      (s - 1) * ∑' n, (u a n : ℝ) ^ (-s) ∧
      (s - 1) * ∑' n, (u a n : ℝ) ^ (-s) ≤
    (l + ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), (n : ℝ) ^ (- s) +
      (s - 1) * ∑' n : T, (u a n : ℝ) ^ (- s) := sorry

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

theorem lemmaZ0 :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℂ) ^ s)
      (𝓝[{s | 1 < s.re}] 1) (𝓝 1) := by
  have : Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝[{s | 1 < s.re}] 1) (𝓝 1) := by
    refine Filter.Tendsto.mono_left riemannZeta_residue_one ?_
    refine nhdsWithin_mono _ ?_
    aesop
  refine Tendsto.congr' ?_ this
  rw [eventuallyEq_nhdsWithin_iff]
  refine Eventually.of_forall (fun s hs ↦ ?_)
  exact congr_arg ((s - 1) * ·) (zeta_eq_tsum_one_div_nat_cpow hs)

theorem lemmaZ1 :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℝ) ^ s)
      (𝓝[>] 1) (𝓝 1) := by
  have t₀ : Tendsto Complex.ofReal' (𝓝[≠] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds (Complex.continuous_ofReal.tendsto 1)
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    rwa [Set.mem_compl_singleton_iff, ne_eq, ← Complex.ofReal_inj, Complex.ofReal_one] at hx
  have t₁ := riemannZeta_residue_one
  have := t₁.comp t₀
  simp [Function.comp_def] at this
  have t₁ := Complex.one_re ▸ Complex.continuous_re.tendsto 1
  have := t₁.comp this
  simp [Function.comp_def] at this
  refine Tendsto.congr' ?_ (Filter.Tendsto.mono_left this ?_)
  · filter_upwards [eventually_mem_nhdsWithin] with s hs
    rw [zeta_eq_tsum_one_div_nat_cpow]
    rw [show (∑' (n : ℕ), 1 / (n : ℂ) ^ (s : ℂ)).re =
      Complex.reCLM (∑' (n : ℕ), 1 / (n : ℂ) ^ (s : ℂ)) by rfl]
    simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow sorry, one_div, ← Complex.ofReal_inv]
    rw [Complex.reCLM.map_tsum]
    simp_rw [Complex.reCLM_apply, Complex.ofReal_re]
    rw [Complex.summable_ofReal]
    rw [Real.summable_nat_rpow_inv]
    exact hs
    simp
    exact hs
  · refine nhdsWithin_mono _ ?_
    aesop

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

#exit

  have t₁ : Tendsto (fun s ↦ c ^ s)  (𝓝[>] 1) (𝓝 c) := sorry
  have t₂ : Tendsto (fun s : ℝ ↦ ∑' n, (n : ℝ) ^ (- s)) (𝓝[>] 1) (𝓝 1) := sorry
  have : ∀ s : ℝ, Summable (fun n ↦ (n : ℝ) ^ (- s)) := sorry
  have := fun s : ℝ ↦
    (sum_add_tsum_compl (β := ℕ) (α := ℝ) (s := T) (f := fun n ↦ (n : ℝ) ^ (- s)) sorry).symm


  sorry







#exit


  have h₁ : Tendsto (fun n ↦ (A a (u a n) : ℝ)/ (u a n)) atTop (𝓝 l) := hA₁.comp (lemma21 ha)
  have h₂ : Tendsto (fun n : ℕ ↦ (A a (u a (n + 1)) : ℝ) / (u a (n + 1)) * ((n + 1 : ℝ) / n))
      atTop (𝓝 l) := sorry
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h₁ h₂ ?_ ?_
  · filter_upwards with n
    refine div_le_div_of_nonneg_right ?_ ?_
    · rw [Nat.cast_le]
      exact lemma11 ha n
    · exact Nat.cast_nonneg _
  ·
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← inv_mul_le_iff₀', inv_div, mul_comm, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ ?_
    · rw [Nat.cast_le]
      exact (lemma12 u n).le
    · exact Nat.cast_nonneg _
    · rw [Nat.cast_ne_zero]
      exact Nat.not_eq_zero_of_lt hn
    · refine div_pos ?_ ?_
      · rw [Nat.cast_pos]
        have := lemma22 u (Nat.le_succ n)
        exact lt_of_lt_of_le hn this
      · rw [Nat.cast_pos]
        exact hn

#exit

local instance (n : ℕ) : Fintype {k : ℕ | A a (k - 1) ≤ n} := sorry -- hu₂ n

include ha in
theorem lemma01 (n : ℕ) : {k : ℕ | A a (k - 1) ≤ n}.toFinset.Nonempty := ⟨0, by simp [A, ha]⟩

-- def u (n : ℕ) : ℕ := Finset.max' {k : ℕ | A a (k - 1) ≤ n}.toFinset (lemma01 ha n)

theorem lemma11 (n : ℕ) : A a ((u ha n) - 1) ≤ n := by
  have := Finset.max'_mem {k : ℕ | A a (k - 1) ≤ n}.toFinset (lemma01 ha _)
  rwa [Set.mem_toFinset, Set.mem_setOf_eq] at this

theorem lemma12 (n : ℕ) : n < A a (u ha n) := by
  by_contra! h
  have := Finset.le_max' {k : ℕ | A a (k - 1) ≤ n}.toFinset (u ha n + 1) ?_
  · simp [u] at this
  · rwa [Set.mem_toFinset, Set.mem_setOf_eq, add_tsub_cancel_right]

set_option maxHeartbeats 0

include hl hA₁ in
theorem lemma2 : Tendsto (A a) atTop atTop := by
  have : Tendsto (fun n ↦ (A a n : ℝ)) atTop atTop := by
    have : Tendsto (fun n : ℕ ↦ l * (n : ℝ)) atTop atTop := by
      refine Tendsto.const_mul_atTop hl tendsto_natCast_atTop_atTop
    refine Asymptotics.IsEquivalent.tendsto_atTop ?_ this
    rw [Asymptotics.isEquivalent_comm, Asymptotics.isEquivalent_iff_tendsto_one]
    convert Tendsto.mul hA₁ (tendsto_const_nhds (x := l⁻¹))
    · dsimp
      ring
    · rw [mul_inv_cancel₀ hl.ne']
    · filter_upwards [eventually_ne_atTop 0] with n hn
      refine mul_ne_zero hl.ne' (Nat.cast_ne_zero.mpr hn)
  exact tendsto_natCast_atTop_iff.mp this

include ha in
theorem lemma_main (n : ℕ) : Nat.card {k | u ha k = n} = a n := by
  obtain hn | hn := Nat.eq_zero_or_pos n
  · rw [hn, ha]
    sorry
  · have : {k | u ha k = n} = Finset.Ico (A a (n - 1)) (A a n) := by
      ext x
      rw [Set.mem_setOf_eq, Finset.coe_Ico, Set.mem_Ico]
      refine ⟨?_, ?_⟩
      · intro h
        rw [← h]
        refine ⟨lemma11 ha x, lemma12 ha x⟩
      · intro h
        refine le_antisymm ?_ ?_
        · sorry
        · sorry
    simp_rw [this, Nat.card_eq_card_toFinset, Finset.coe_Ico, Set.toFinset_Ico, Nat.card_Ico]
    simp_rw [A]
    rw [Finset.sum_range_succ]
    rw [Nat.sub_add_eq_max]
    have : max n 1 = n := sorry
    rw [this, Nat.add_sub_cancel_left]

theorem lemma22 : Monotone (u ha) := by
  intro n m h
  rw [u, Finset.max'_le_iff]
  intro k hk
  refine Finset.le_max' _ _ ?_
  rw [Set.mem_toFinset, Set.mem_setOf_eq] at hk ⊢
  exact le_trans hk h

theorem lemma21 : Tendsto (u ha) atTop atTop := by
  refine Monotone.tendsto_atTop_atTop (lemma22 ha) ?_
  sorry



-- theorem lemma22 : Monotone (s u) := sorry

include hA₁ in
theorem lemma3 : Tendsto (fun n : ℕ ↦ (n : ℝ) / (u ha n)) atTop (𝓝 l) := by
  have h₁ : Tendsto (fun n ↦ (A a (u ha n) : ℝ)/ (u ha n)) atTop (𝓝 l) := hA₁.comp (lemma21 ha)
  have h₂ : Tendsto (fun n : ℕ ↦ (A a (u ha (n + 1)) : ℝ) / (u ha (n + 1)) * ((n + 1 : ℝ) / n))
      atTop (𝓝 l) := sorry
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h₁ h₂ ?_ ?_
  · filter_upwards with n
    refine div_le_div_of_nonneg_right ?_ ?_
    · rw [Nat.cast_le]
      exact lemma11 ha n
    · exact Nat.cast_nonneg _
  ·
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← inv_mul_le_iff₀', inv_div, mul_comm, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ ?_
    · rw [Nat.cast_le]
      exact (lemma12 u n).le
    · exact Nat.cast_nonneg _
    · rw [Nat.cast_ne_zero]
      exact Nat.not_eq_zero_of_lt hn
    · refine div_pos ?_ ?_
      · rw [Nat.cast_pos]
        have := lemma22 u (Nat.le_succ n)
        exact lt_of_lt_of_le hn this
      · rw [Nat.cast_pos]
        exact hn







#exit


theorem main {u : ℕ → ℝ} {l : ℝ} (h : Tendsto (fun n ↦ (u n)/ n) atTop (𝓝 l)) :
    Tendsto (fun s ↦ (s - 1) * ∑' n, (u n) ^ (- s)) (𝓝[>] 1) (𝓝 l) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [NormedAddCommGroup.tendsto_atTop] at h
  specialize h ε hε
  obtain ⟨N₀, hN⟩ := h
  simp_rw [Real.norm_eq_abs, abs_lt, ← neg_add_eq_sub, lt_neg_add_iff_add_lt,
    neg_add_lt_iff_lt_add, ← sub_eq_add_neg] at hN
  have h₀ : ∀ s : ℝ, (l - ε) * ∑' n : ↑(Finset.range N₀ : Set ℕ)ᶜ, (n : ℝ) ^ (- s) ≤
       ∑' n : ↑(Finset.range N₀ : Set ℕ)ᶜ, (u n) ^ (- s) := sorry
  have h₁ : ∀ s : ℝ, ∑' n : ↑(Finset.range N₀ : Set ℕ)ᶜ, (u n) ^ (- s) ≤
      (l + ε) * ∑' n : ↑(Finset.range N₀ : Set ℕ)ᶜ, (n : ℝ) ^ (- s) := sorry
  have h₃ : Tendsto (fun s ↦ (s - 1) *  ∑' n : ↑(Finset.range N₀ : Set ℕ)ᶜ, (n : ℝ) ^ (- s))
      (𝓝[>] 1) (𝓝 1) := sorry

  simp_rw [Real.norm_eq_abs, abs_lt, ← neg_add_eq_sub, lt_neg_add_iff_add_lt,
    neg_add_lt_iff_lt_add, ← sub_eq_add_neg, div_lt_iff₀ sorry, lt_div_iff₀ sorry] at hN

  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
  · refine le_of_frequently_sub_le (Eventually.frequently ?_)
    sorry
  · sorry




#exit


example (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto (fun n ↦ (∑ i ∈ Finset.range n, a i) /n) atTop (𝓝 c)) :
    Tendsto (fun s : ℝ ↦ ∑' n, (a n) * (n : ℝ) ^ (-s)) (𝓝[<] 1) (𝓝 c) := by
  let A : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range n, a i
  have h0 : Tendsto (fun n ↦ (A n) / n) atTop (𝓝 c) := sorry
  have h1 : ∀ n, 1 ≤ n → a n = A n - A (n - 1) := sorry
  have h2 : ∀ s : ℝ, ∑' n, (a n) * (n : ℝ) ^ (-s) = ∑' n, (A n) * (n : ℝ) ^ (-s) -
      ∑' n, (A (n - 1)) * (n : ℝ) ^ (-s) := sorry
  have h3 : ∀ s : ℝ,  ∑' n, (a n) * (n : ℝ) ^ (-s) = ∑' n, (A n) * (n : ℝ) ^ (-s) -
      ∑' n, (A n) * (n + 1 : ℝ) ^ (-s) := sorry
  simp_rw [h3]
  simp_rw [← tsum_sub sorry sorry]
  simp_rw [← mul_sub]

  sorry
