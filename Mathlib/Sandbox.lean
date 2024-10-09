import Mathlib

open Filter Topology

section Eventually

theorem le_of_frequently_sub_le {α : Type*} [LinearOrderedField α] [TopologicalSpace α]
    [OrderTopology α] {a b : α} (h : ∃ᶠ ε in 𝓝[>] 0, b - ε ≤ a) : b ≤ a := by
  contrapose! h
  obtain ⟨c, hc⟩ := exists_add_lt_and_pos_of_lt h
  refine not_frequently.mpr <|
    eventually_iff_exists_mem.mpr ⟨Set.Ioc 0 c, Ioc_mem_nhdsWithin_Ioi' hc.2, fun _ hx ↦ ?_⟩
  exact not_le.mpr <| lt_of_lt_of_le (lt_tsub_of_add_lt_right hc.1) (sub_le_sub_left hx.2 b)

theorem le_of_frequently_le_add {α : Type*} [LinearOrderedField α] [TopologicalSpace α]
    [OrderTopology α] {a b : α} (h : ∃ᶠ ε in 𝓝[>] 0, b ≤ a + ε) : b ≤ a := by
  simp_rw [← sub_le_iff_le_add] at h
  exact le_of_frequently_sub_le h

end Eventually

-- theorem sum_add_tsum_compl {α : Type u_1}  {β : Type u_2}  [AddCommGroup α]  [TopologicalSpace α] [TopologicalAddGroup α]  {f : β → α}  [T2Space α]  {s : Finset β} (hf : Summable f) :
-- ∑ x ∈ s, f x + ∑' (x : ↑(↑s)ᶜ), f ↑x = ∑' (x : β), f x

open Classical in
theorem zap {α β γ : Type*} [Ring α] [TopologicalSpace α] [TopologicalSpace γ]
    [TopologicalAddGroup α] -- [TopologicalRing α]?
    {f : β → γ → α} [T2Space α] {s : Finset β} (hf₁ : Summable f) {l : γ} {t : Set γ}
    (hf₂ : ∀ i, ContinuousWithinAt (f i) t l) {g : γ → α} (hg : g l = 0) :
    Tendsto (fun x ↦ (g x) * ∑' i : ↑(s : Set β)ᶜ, (f i x)) (𝓝[t] l) (𝓝 (∑' i, f i l)) := by
  sorry

noncomputable section

example {u : ℕ → ℝ} {t : Finset ℕ} {l : ℝ}
    (hu : Tendsto (fun s : ℝ ↦ (s - 1) * ∑' i, (u i) ^ s) (𝓝[>] 1) (𝓝 l)) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' i : ↑(t : Set ℕ)ᶜ, (u i) ^ s) (𝓝[>] 1) (𝓝 l) := sorry

variable (u : ℕ → ℕ) {l : ℝ} (hl : l ≠ 0)

def A (x : ℝ) : ℕ := Nat.card {k | u k ≤ x}

variable (hu₁ : Tendsto (fun x : ℝ ↦ (A u x : ℝ) / x) atTop (𝓝 l))

local instance (n : ℕ) : Fintype {k : ℕ | A u k ≤ n} := sorry

def s (n : ℕ) : ℕ := Finset.sup {k : ℕ | A u k ≤ n}.toFinset (fun n ↦ n)

theorem lemma1 (n : ℕ) : Nat.card {k | u k ≤ s n} ≤ n := sorry






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
