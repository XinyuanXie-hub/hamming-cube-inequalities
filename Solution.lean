import Solution.ConcreteProfile

open scoped BigOperators

namespace HammingCube

abbrev Cube (n : ℕ) := Fin n → Bool

def flip {n : ℕ} (x : Cube n) (i : Fin n) : Cube n :=
  Function.update x i (!x i)

noncomputable def avg {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x, f x) / (2 : ℝ) ^ n

noncomputable def density {n : ℕ} (A : Finset (Cube n)) : ℝ :=
  (A.card : ℝ) / (2 : ℝ) ^ n

/- Discrete cube identities and the Bellman induction. -/

theorem flip_flip {n : ℕ} (x : Cube n) (i : Fin n) : flip (flip x i) i = x := by
  funext j
  by_cases h : j = i
  · subst j; simp [flip]
  · simp [flip, h]

theorem hc_mean {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (b : Bool)
    (hf : ∀ x, f x = if x i = b then 1 else 0) : avg f = 1 / 2 := by
  let e : Cube n ≃ Cube n :=
    { toFun := fun x => flip x i
      invFun := fun x => flip x i
      left_inv := fun x => flip_flip x i
      right_inv := fun x => flip_flip x i }
  have hflip (x : Cube n) : f (flip x i) = 1 - f x := by
    rw [hf, hf]
    cases hx : x i <;> cases b <;> simp [flip, hx]
  have hs := e.sum_comp f
  change (∑ x, f (flip x i)) = ∑ x, f x at hs
  simp_rw [hflip] at hs
  rw [Finset.sum_sub_distrib] at hs
  have hcard : (∑ _ : Cube n, (1 : ℝ)) = (2 : ℝ)^n := by simp
  rw [hcard] at hs
  unfold avg
  apply (div_eq_iff (by positivity : (2 : ℝ)^n ≠ 0)).2
  linarith

theorem hc_gradient {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (b : Bool)
    (hf : ∀ x, f x = if x i = b then 1 else 0) (x : Cube n) :
    Real.sqrt (∑ j : Fin n, ((f x - f (flip x j)) / 2)^2) = 1 / 2 := by
  have hs : (∑ j : Fin n, ((f x - f (flip x j)) / 2)^2) = (1 : ℝ)/4 := by
    rw [Finset.sum_eq_single i]
    · rw [hf, hf]
      cases hx : x i <;> cases b <;> norm_num [flip, hx]
    · intro j _ hji
      have he : f (flip x j) = f x := by simp [hf, flip, Ne.symm hji]
      rw [he]
      simp
    · simp
  rw [hs]
  norm_num

theorem half_cube_equality {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (b : Bool)
    (hf : ∀ x, f x = if x i = b then 1 else 0) :
    avg (fun x => |f x - avg f|) =
      avg (fun x => Real.sqrt (∑ j : Fin n, ((f x - f (flip x j)) / 2)^2)) := by
  have hd (x : Cube n) : |f x - avg f| = (1 : ℝ)/2 := by
    rw [hc_mean f i b hf, hf]
    split_ifs <;> norm_num
  simp_rw [hd, hc_gradient f i b hf]

noncomputable def flipEquiv {n : ℕ} (i : Fin n) : Cube n ≃ Cube n where
  toFun := fun x => flip x i
  invFun := fun x => flip x i
  left_inv := fun x => flip_flip x i
  right_inv := fun x => flip_flip x i

lemma crossing_symm {n : ℕ} (A B : Finset (Cube n)) :
    (∑ x ∈ A, ((Finset.univ.filter (fun i => flip x i ∈ B)).card : ℝ)) =
    ∑ x ∈ B, ((Finset.univ.filter (fun i => flip x i ∈ A)).card : ℝ) := by
  classical
  have expand (S T : Finset (Cube n)) :
      (∑ x ∈ S, ((Finset.univ.filter (fun i => flip x i ∈ T)).card : ℝ)) =
        ∑ i : Fin n, ∑ x : Cube n, if x ∈ S ∧ flip x i ∈ T then (1 : ℝ) else 0 := by
    simp_rw [Finset.cast_card, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    symm
    calc
      _ = ∑ x : Cube n, if x ∈ S then (if flip x i ∈ T then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp_all
      _ = _ := by rw [← Finset.sum_filter]; simp
  rw [expand, expand]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ x : Cube n, if flip x i ∈ B ∧ flip (flip x i) i ∈ A then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [flip_flip, and_comm]
    _ = _ := (flipEquiv i).sum_comp (fun x => if x ∈ B ∧ flip x i ∈ A then (1 : ℝ) else 0)

lemma sqrt_nat_le (k : ℕ) : Real.sqrt (k : ℝ) ≤ k := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · by_cases hk : k = 0
    · simp [hk]
    · have h : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      nlinarith

theorem theorem_1_2_of_isoperimetric (n : ℕ) (hn : 1 ≤ n)
    (iso : ∀ (S : Finset (Cube n)), density S ≤ 1 / 2 →
      let h := fun x : Cube n =>
        if x ∈ S then ((Finset.univ.filter (fun i => flip x i ∉ S)).card : ℝ) else 0
      density S * Real.sqrt (Real.logb 2 (1 / density S)) ≤
        avg (fun x => Real.sqrt (h x)))
    (A B W : Finset (Cube n))
    (hAB : Disjoint A B) (hAW : Disjoint A W) (hBW : Disjoint B W)
    (hcover : A ∪ B ∪ W = Finset.univ) (hA : density A = 1 / 2) :
    let edgeMeasure :=
      (∑ x ∈ A, ((Finset.univ.filter (fun i => flip x i ∈ B)).card : ℝ)) /
        (2 : ℝ) ^ n
    (1 : ℝ) / 2 ≤ edgeMeasure + Real.sqrt (n : ℝ) * density W := by
  classical
  have hC : B ∪ W = Aᶜ := by
    ext x
    have hab := Finset.disjoint_left.mp hAB
    have haw := Finset.disjoint_left.mp hAW
    have hc : x ∈ A ∨ x ∈ B ∨ x ∈ W := by
      have : x ∈ A ∪ B ∪ W := by rw [hcover]; simp
      simpa only [Finset.mem_union, or_assoc] using this
    simp only [Finset.mem_union, Finset.mem_compl]
    constructor
    · intro hx ha
      rcases hx with hb | hw
      · exact hab ha hb
      · exact haw ha hw
    · intro hx
      rcases hc with ha | hb | hw
      · exact False.elim (hx ha)
      · exact Or.inl hb
      · exact Or.inr hw
  have hcard : Fintype.card (Cube n) = 2 ^ n := by simp [Cube, Fintype.card_pi]
  have hden : density (B ∪ W) = 1 / 2 := by
    rw [hC]
    unfold density at *
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ A), hcard]
    push_cast
    have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp at hA ⊢
    linarith
  have hbase := iso (B ∪ W) (le_of_eq hden)
  dsimp only at hbase
  rw [hden] at hbase
  norm_num [Real.logb_self_eq_one] at hbase
  have hpoint (x : Cube n) :
      Real.sqrt (if x ∈ B ∪ W then
        ((Finset.univ.filter (fun i => flip x i ∉ B ∪ W)).card : ℝ) else 0) ≤
      (if x ∈ B then ((Finset.univ.filter (fun i => flip x i ∈ A)).card : ℝ) else 0) +
      (if x ∈ W then Real.sqrt (n : ℝ) else 0) := by
    have hout (i : Fin n) : flip x i ∉ B ∪ W ↔ flip x i ∈ A := by simp [hC]
    simp_rw [hout]
    by_cases hb : x ∈ B
    · have hw : x ∉ W := fun hw => Finset.disjoint_left.mp hBW hb hw
      simp only [Finset.mem_union, hb, true_or, hw, ite_true, ite_false, add_zero]
      exact sqrt_nat_le _
    · by_cases hw : x ∈ W
      · simp only [Finset.mem_union, hb, false_or, hw, ite_true, ite_false, zero_add]
        apply Real.sqrt_le_sqrt
        exact_mod_cast (show (Finset.univ.filter (fun i : Fin n => flip x i ∈ A)).card ≤ n by
          simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => flip x i ∈ A))
      · simp [hb, hw]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) => hpoint x)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul] at hsum
  change (1 : ℝ) / 2 ≤ _
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hbound := div_le_div_of_nonneg_right hsum (le_of_lt hp)
  rw [← crossing_symm A B] at hbound
  unfold avg at hbase
  unfold density
  calc
    (1 : ℝ) / 2 ≤
        (∑ x : Cube n, Real.sqrt (if x ∈ B ∪ W then
          ((Finset.univ.filter (fun i => flip x i ∉ B ∪ W)).card : ℝ) else 0)) /
            (2 : ℝ) ^ n := by
      simpa only [Finset.mem_union, not_or] using hbase
    _ ≤ ((∑ x ∈ A, ((Finset.univ.filter (fun i => flip x i ∈ B)).card : ℝ)) +
        (W.card : ℝ) * Real.sqrt (n : ℝ)) / (2 : ℝ) ^ n := hbound
    _ = _ := by ring

lemma cube_card (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]
lemma avg_const (n : ℕ) (c : ℝ) : avg (fun _ : Cube n => c) = c := by
  simp [avg, mul_div_cancel_left₀]
lemma avg_nonneg {n : ℕ} {f : Cube n → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => h x)) (by positivity)
lemma avg_le_one {n : ℕ} {f : Cube n → ℝ} (h : ∀ x, f x ≤ 1) : avg f ≤ 1 := by
  calc
    avg f ≤ avg (fun _ : Cube n => (1 : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum (fun x _ => h x)
    _ = 1 := avg_const n 1
lemma boolean_deviation {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    avg (fun x => |f x - avg f|) = 2 * avg f * (1 - avg f) := by
  have h0 : 0 ≤ avg f := avg_nonneg (fun x => by rcases hf x with h | h <;> simp [h])
  have h1 : avg f ≤ 1 := avg_le_one (fun x => by rcases hf x with h | h <;> simp [h])
  have hx (x : Cube n) : |f x - avg f| = f x * (1 - 2 * avg f) + avg f := by
    rcases hf x with h | h
    · simp [h, abs_of_nonneg h0]
    · rw [h, abs_of_nonneg (sub_nonneg.mpr h1)]; ring
  simp_rw [hx]
  unfold avg
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [Finset.sum_const, Finset.card_univ, cube_card, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring
lemma boolean_gradient {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (x : Cube n) :
    Real.sqrt (∑ i : Fin n, ((f x - f (flip x i)) / 2) ^ 2) =
      Real.sqrt ((Finset.univ.filter (fun i => f x ≠ f (flip x i))).card : ℝ) / 2 := by
  classical
  have hi (i : Fin n) : ((f x - f (flip x i)) / 2) ^ 2 =
      (if f x ≠ f (flip x i) then (1 : ℝ) else 0) / 4 := by
    rcases hf x with h | h <;> rcases hf (flip x i) with h' | h' <;>
      norm_num [h, h']
  simp_rw [hi]
  rw [← Finset.sum_div]
  have hc : (∑ i : Fin n, if f x ≠ f (flip x i) then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => f x ≠ f (flip x i))).card : ℝ) := by
    exact Finset.sum_boole _ _
  rw [hc, Real.sqrt_div (by positivity)]
  norm_num
noncomputable def poincareBoundary {n : ℕ} (A : Finset (Cube n)) (x : Cube n) : ℝ :=
  if x ∈ A then ((Finset.univ.filter (fun i => flip x i ∉ A)).card : ℝ) else 0

lemma poincare_of_profile {n : ℕ} (B : ℝ → ℝ)
    (hiso : ∀ A : Finset (Cube n), B (density A) ≤
      avg (fun x => Real.sqrt (poincareBoundary A x)))
    (hsym : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 4 * t * (1 - t) ≤ B t + B (1 - t))
    (f : Cube n → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    avg (fun x => |f x - avg f|) ≤
      avg (fun x => Real.sqrt (∑ i : Fin n, ((f x - f (flip x i)) / 2) ^ 2)) := by
  classical
  let A : Finset (Cube n) := Finset.univ.filter (fun x => f x = 1)
  let C : Finset (Cube n) := Finset.univ.filter (fun x => f x = 0)
  have hA : density A = avg f := by
    unfold density avg
    congr 1
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    rcases hf x with h | h <;> simp [h]
  have hC : density C = 1 - avg f := by
    have hi (x : Cube n) : (if f x = 0 then (1 : ℝ) else 0) = 1 - f x := by
      rcases hf x with h | h <;> simp [h]
    unfold density avg
    change ((Finset.univ.filter (fun x => f x = 0)).card : ℝ) / _ = _
    rw [← Finset.sum_boole]
    simp_rw [hi]
    rw [Finset.sum_sub_distrib, sub_div]
    have hc : (∑ _ : Cube n, (1 : ℝ)) / 2 ^ n = 1 := avg_const n 1
    rw [hc]
  have hsplit (x : Cube n) :
      Real.sqrt (poincareBoundary A x) + Real.sqrt (poincareBoundary C x) =
      Real.sqrt ((Finset.univ.filter (fun i => f x ≠ f (flip x i))).card : ℝ) := by
    rcases hf x with hx | hx
    · simp only [poincareBoundary, A, C, Finset.mem_filter, Finset.mem_univ,
        true_and, hx]
      norm_num
      congr 3
      ext i
      exact ne_comm
    · simp only [poincareBoundary, A, C, Finset.mem_filter, Finset.mem_univ,
        true_and, hx]
      norm_num
      congr 3
      ext i
      exact ne_comm
  have hg : avg (fun x => Real.sqrt (∑ i : Fin n,
      ((f x - f (flip x i)) / 2) ^ 2)) =
      (avg (fun x => Real.sqrt (poincareBoundary A x)) +
       avg (fun x => Real.sqrt (poincareBoundary C x))) / 2 := by
    simp_rw [boolean_gradient f hf, ← hsplit]
    unfold avg
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    ring
  rw [boolean_deviation f hf, hg]
  have ha := hiso A
  have hc := hiso C
  rw [hA] at ha
  rw [hC] at hc
  have h0 : 0 ≤ avg f := avg_nonneg (fun x => by rcases hf x with h | h <;> simp [h])
  have h1 : avg f ≤ 1 := avg_le_one (fun x => by rcases hf x with h | h <;> simp [h])
  have hh := hsym (avg f) h0 h1
  linarith

/-- Full approved Poincaré conclusion, conditional on an isoperimetric profile. -/
theorem theorem_1_3_of_profile {n : ℕ} (B : ℝ → ℝ)
    (hiso : ∀ A : Finset (Cube n), B (density A) ≤
      avg (fun x => Real.sqrt (poincareBoundary A x)))
    (hsym : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 4 * t * (1 - t) ≤ B t + B (1 - t))
    (f : Cube n → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    let gradient := fun x : Cube n =>
      Real.sqrt (∑ i : Fin n, ((f x - f (flip x i)) / 2) ^ 2)
    let deviation := avg (fun x => |f x - avg f|)
    deviation ≤ avg gradient ∧
      (∀ (i : Fin n) (b : Bool),
        (∀ x, f x = if x i = b then 1 else 0) → deviation = avg gradient) := by
  exact ⟨poincare_of_profile B hiso hsym f hf,
    fun i b hi => half_cube_equality f i b hi⟩

def cubeSlice {n : ℕ} (A : Finset (Cube (n + 1))) (b : Bool) : Finset (Cube n) :=
  Finset.univ.filter (fun x => Fin.cons b x ∈ A)

lemma avg_slice {n : ℕ} (f : Cube (n + 1) → ℝ) :
    avg f = (avg (fun x => f (Fin.cons false x)) +
      avg (fun x => f (Fin.cons true x))) / 2 := by
  have hs := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f
  change (∑ x : Bool × Cube n, f (Fin.cons x.1 x.2)) = ∑ x, f x at hs
  rw [Fintype.sum_prod_type] at hs
  simp only [Fintype.sum_bool] at hs
  unfold avg
  rw [← hs, pow_succ]
  ring

lemma density_eq_avg_indicator {n : ℕ} (A : Finset (Cube n)) :
    density A = avg (fun x => if x ∈ A then 1 else 0) := by
  unfold density avg
  congr 1
  simp

lemma density_slice {n : ℕ} (A : Finset (Cube (n + 1))) :
    density A = (density (cubeSlice A false) + density (cubeSlice A true)) / 2 := by
  rw [density_eq_avg_indicator, avg_slice]
  simp only [density_eq_avg_indicator, cubeSlice, Finset.mem_filter, Finset.mem_univ,
    true_and]

lemma flip_cons_zero {n : ℕ} (b : Bool) (x : Cube n) :
    flip (Fin.cons b x) 0 = Fin.cons (!b) x := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [flip]
  · simp [flip, Fin.succ_ne_zero]

lemma flip_cons_succ {n : ℕ} (b : Bool) (x : Cube n) (i : Fin n) :
    flip (Fin.cons b x) i.succ = Fin.cons b (flip x i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [flip, Ne.symm (Fin.succ_ne_zero i)]
  · by_cases h : k = i
    · subst k; simp [flip]
    · simp [flip, h]

noncomputable def outwardDegree {n : ℕ} (A : Finset (Cube n)) (x : Cube n) : ℝ :=
  if x ∈ A then ((Finset.univ.filter (fun i => flip x i ∉ A)).card : ℝ) else 0

lemma outwardDegree_slice {n : ℕ} (A : Finset (Cube (n + 1))) (b : Bool)
    (x : Cube n) :
    outwardDegree A (Fin.cons b x) = outwardDegree (cubeSlice A b) x +
      if x ∈ cubeSlice A b ∧ x ∉ cubeSlice A (!b) then 1 else 0 := by
  simp only [outwardDegree, cubeSlice, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hx : Fin.cons b x ∈ A
  · simp only [hx, ite_true, true_and]
    rw [Finset.cast_card, Finset.sum_filter, Fin.sum_univ_succ]
    simp only [flip_cons_zero, flip_cons_succ]
    rw [Finset.cast_card, Finset.sum_filter]
    ring
  · simp [hx]

lemma sqrt_nat_add_one (k : ℕ) :
    1 + (Real.sqrt 2 - 1) * Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
  by_cases hk : k = 0
  · simp [hk]
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  have ht : 1 ≤ Real.sqrt (k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have ht2 := Real.sq_sqrt (show 0 ≤ (k : ℝ) by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have hp : 0 ≤ 2 * (Real.sqrt 2 - 1) * Real.sqrt (k : ℝ) * (Real.sqrt (k : ℝ) - 1) := by positivity
  apply Real.le_sqrt_of_sq_le
  nlinarith

lemma sqrt_sum_pair_le {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    Real.sqrt ((∑ i ∈ s, u i)^2 + (∑ i ∈ s, v i)^2) ≤
      ∑ i ∈ s, Real.sqrt ((u i)^2 + (v i)^2) := by
  let z (i : ι) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![u i, v i]
  have h := norm_sum_le s z
  simpa [EuclideanSpace.norm_eq, z, Fin.sum_univ_two, Real.norm_eq_abs]
    using h

lemma sqrt_avg_pair_le {n : ℕ} (u v : Cube n → ℝ) :
    Real.sqrt ((avg u)^2 + (avg v)^2) ≤
      avg (fun x => Real.sqrt ((u x)^2 + (v x)^2)) := by
  have h := sqrt_sum_pair_le Finset.univ u v
  have heq : (avg u)^2 + (avg v)^2 =
      ((∑ x, u x)^2 + (∑ x, v x)^2) / ((2 : ℝ)^n)^2 := by
    unfold avg
    ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  exact div_le_div_of_nonneg_right h (by positivity)

lemma sqrt_nat_add_bool (k : ℕ) (b : Bool) :
    (if b then (1 : ℝ) else 0) + (Real.sqrt 2 - 1) * Real.sqrt (k : ℝ) ≤
      Real.sqrt ((k : ℝ) + if b then 1 else 0) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero]
    have hs : Real.sqrt (2 : ℝ) ≤ 2 := by
      apply Real.sqrt_le_iff.mpr
      norm_num
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  · simpa using sqrt_nat_add_one k

lemma avg_sqrt_nat_add_bool_linear {n : ℕ} (k : Cube n → ℕ) (b : Cube n → Bool) :
    avg (fun x => if b x then (1 : ℝ) else 0) +
      (Real.sqrt 2 - 1) * avg (fun x => Real.sqrt (k x : ℝ)) ≤
      avg (fun x => Real.sqrt ((k x : ℝ) + if b x then 1 else 0)) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Cube n)))
    (fun x _ => sqrt_nat_add_bool (k x) (b x))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hh := div_le_div_of_nonneg_right h (show 0 ≤ (2 : ℝ)^n by positivity)
  simpa only [avg, add_div, mul_div_assoc] using hh

lemma avg_sqrt_nat_add_bool_quadratic {n : ℕ} (k : Cube n → ℕ) (b : Cube n → Bool) :
    Real.sqrt ((avg (fun x => Real.sqrt (k x : ℝ)))^2 +
      (avg (fun x => if b x then (1 : ℝ) else 0))^2) ≤
      avg (fun x => Real.sqrt ((k x : ℝ) + if b x then 1 else 0)) := by
  have h := sqrt_avg_pair_le (fun x => Real.sqrt (k x : ℝ))
    (fun x => if b x then (1 : ℝ) else 0)
  have he (x : Cube n) : (Real.sqrt (k x : ℝ))^2 +
      (if b x then (1 : ℝ) else 0)^2 = (k x : ℝ) + if b x then 1 else 0 := by
    rw [Real.sq_sqrt (by positivity)]
    cases b x <;> norm_num
  simpa only [he] using h

lemma bellman_step (B : ℝ → ℝ) (a b u v d t : ℝ)
    (_ha : 0 ≤ a) (hab : a ≤ b) (_hb : b ≤ 1)
    (hBa : B a ≤ u) (hBb : B b ≤ v) (hBbn : 0 ≤ B b)
    (hd : b - a ≤ d)
    (hquad : (u + Real.sqrt (v^2 + d^2)) / 2 ≤ t)
    (hlinear : (u + d + (Real.sqrt 2 - 1) * v) / 2 ≤ t)
    (htwo : 0 ≤ max
      (Real.sqrt ((b-a)^2 + (B b)^2) + B a - 2 * B ((a+b)/2))
      (b-a + (Real.sqrt 2-1)*B b + B a - 2*B ((a+b)/2))) :
    B ((a+b)/2) ≤ t := by
  have hd0 : 0 ≤ d := le_trans (sub_nonneg.mpr hab) hd
  have hv0 : 0 ≤ v := le_trans hBbn hBb
  have hs : 0 ≤ Real.sqrt (2 : ℝ) - 1 := by
    have := Real.one_le_sqrt.mpr (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  rcases le_max_iff.mp htwo with h | h
  · have hroot : Real.sqrt ((b-a)^2 + (B b)^2) ≤ Real.sqrt (v^2+d^2) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    linarith
  · have hp := mul_le_mul_of_nonneg_left hBb hs
    linarith

lemma ind_avg_mono {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x ≤ g x) :
    avg f ≤ avg g := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun x _ => h x)

lemma ind_avg_sub {n : ℕ} (f g : Cube n → ℝ) :
    avg (fun x => f x - g x) = avg f - avg g := by
  simp [avg, Finset.sum_sub_distrib, sub_div]

lemma ind_density_nonneg {n : ℕ} (A : Finset (Cube n)) : 0 ≤ density A := by
  unfold density
  positivity

lemma ind_density_le_one {n : ℕ} (A : Finset (Cube n)) : density A ≤ 1 := by
  have h : A.card ≤ 2^n := by simpa using Finset.card_le_univ A
  unfold density
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast h

lemma slice_difference_bound {n : ℕ} (A : Finset (Cube (n+1))) (b : Bool) :
    density (cubeSlice A b) - density (cubeSlice A (!b)) ≤
      avg (fun x => if x ∈ cubeSlice A b ∧ x ∉ cubeSlice A (!b) then 1 else 0) := by
  rw [density_eq_avg_indicator, density_eq_avg_indicator, ← ind_avg_sub]
  apply ind_avg_mono
  intro x
  by_cases h : x ∈ cubeSlice A b <;> by_cases h' : x ∈ cubeSlice A (!b) <;>
    simp [h, h']

noncomputable def cubeEnergy {n : ℕ} (A : Finset (Cube n)) : ℝ :=
  avg (fun x => Real.sqrt (outwardDegree A x))

noncomputable def sliceLiftEnergy {n : ℕ} (A : Finset (Cube (n+1))) (b : Bool) : ℝ :=
  avg (fun x => Real.sqrt (outwardDegree A (Fin.cons b x)))

lemma cubeEnergy_slices {n : ℕ} (A : Finset (Cube (n+1))) (b : Bool) :
    cubeEnergy A = (sliceLiftEnergy A (!b) + sliceLiftEnergy A b) / 2 := by
  unfold cubeEnergy sliceLiftEnergy
  rw [avg_slice]
  cases b <;> simp; ring

lemma cubeEnergy_slice_le {n : ℕ} (A : Finset (Cube (n+1))) (b : Bool) :
    cubeEnergy (cubeSlice A b) ≤ sliceLiftEnergy A b := by
  apply ind_avg_mono
  intro x
  apply Real.sqrt_le_sqrt
  rw [outwardDegree_slice]
  split_ifs <;> linarith

lemma sliceLiftEnergy_bounds {n : ℕ} (A : Finset (Cube (n+1))) (b : Bool) :
    let d := avg (fun x => if x ∈ cubeSlice A b ∧ x ∉ cubeSlice A (!b) then (1 : ℝ) else 0)
    Real.sqrt ((cubeEnergy (cubeSlice A b))^2 + d^2) ≤ sliceLiftEnergy A b ∧
      d + (Real.sqrt 2 - 1) * cubeEnergy (cubeSlice A b) ≤ sliceLiftEnergy A b := by
  classical
  let k (x : Cube n) : ℕ := if x ∈ cubeSlice A b then
    (Finset.univ.filter (fun i => flip x i ∉ cubeSlice A b)).card else 0
  let bb (x : Cube n) : Bool := decide (x ∈ cubeSlice A b ∧ x ∉ cubeSlice A (!b))
  have hk (x : Cube n) : (k x : ℝ) = outwardDegree (cubeSlice A b) x := by
    simp only [k, outwardDegree]
    split_ifs <;> simp
  have hb (x : Cube n) : (if bb x then (1 : ℝ) else 0) =
      if x ∈ cubeSlice A b ∧ x ∉ cubeSlice A (!b) then 1 else 0 := by simp [bb]
  have hquad := avg_sqrt_nat_add_bool_quadratic k bb
  have hlin := avg_sqrt_nat_add_bool_linear k bb
  dsimp only
  constructor
  · simpa only [hk, hb, ← outwardDegree_slice, cubeEnergy, sliceLiftEnergy] using hquad
  · simpa only [hk, hb, ← outwardDegree_slice, cubeEnergy, sliceLiftEnergy] using hlin

lemma bellman_successor (B : ℝ → ℝ)
    (hpos : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ B t)
    (htwo : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → 0 ≤ max
      (Real.sqrt ((b-a)^2 + (B b)^2) + B a - 2 * B ((a+b)/2))
      (b-a + (Real.sqrt 2-1)*B b + B a - 2*B ((a+b)/2)))
    {n : ℕ} (A : Finset (Cube (n+1))) (b : Bool)
    (horder : density (cubeSlice A (!b)) ≤ density (cubeSlice A b))
    (hsmall : B (density (cubeSlice A (!b))) ≤ cubeEnergy (cubeSlice A (!b)))
    (hbig : B (density (cubeSlice A b)) ≤ cubeEnergy (cubeSlice A b)) :
    B (density A) ≤ cubeEnergy A := by
  let a := density (cubeSlice A (!b))
  let c := density (cubeSlice A b)
  let d := avg (fun x => if x ∈ cubeSlice A b ∧ x ∉ cubeSlice A (!b) then (1 : ℝ) else 0)
  have hsplit := cubeEnergy_slices A b
  have hsmall' := cubeEnergy_slice_le A (!b)
  have hbounds := sliceLiftEnergy_bounds A b
  have hdensity : density A = (a+c)/2 := by
    rw [density_slice]
    dsimp [a,c]
    cases b <;> simp; ring
  rw [hdensity]
  apply bellman_step B a c (cubeEnergy (cubeSlice A (!b)))
    (cubeEnergy (cubeSlice A b)) d (cubeEnergy A)
    (ind_density_nonneg _) horder (ind_density_le_one _) hsmall hbig
    (hpos _ (ind_density_nonneg _) (ind_density_le_one _)) (slice_difference_bound A b)
  · dsimp [d]
    linarith [hbounds.1]
  · dsimp [d]
    linarith [hbounds.2]
  · exact htwo a c (ind_density_nonneg _) horder (ind_density_le_one _)

lemma bellman_isoperimetric (B : ℝ → ℝ) (h0 : B 0 = 0) (h1 : B 1 = 0)
    (hpos : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ B t)
    (htwo : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → 0 ≤ max
      (Real.sqrt ((b-a)^2 + (B b)^2) + B a - 2 * B ((a+b)/2))
      (b-a + (Real.sqrt 2-1)*B b + B a - 2*B ((a+b)/2)))
    (n : ℕ) (A : Finset (Cube n)) :
    B (density A) ≤ avg (fun x => Real.sqrt (outwardDegree A x)) := by
  change B (density A) ≤ cubeEnergy A
  induction n with
  | zero =>
    have hc : A.card ≤ 1 := by simpa using Finset.card_le_univ A
    have he : cubeEnergy A = 0 := by simp [cubeEnergy, avg, outwardDegree]
    rw [he]
    unfold density
    interval_cases A.card <;> simp [h0, h1]
  | succ n ih =>
    by_cases horder : density (cubeSlice A false) ≤ density (cubeSlice A true)
    · exact bellman_successor B hpos htwo A true horder (ih _) (ih _)
    · exact bellman_successor B hpos htwo A false (le_of_not_ge horder) (ih _) (ih _)

/-- The concrete scalar profile gives the all-dimensional cube inequality. -/
theorem profile_isoperimetric (n : ℕ) (A : Finset (Cube n)) :
    HammingCubeConcrete.B (density A) ≤ avg (fun x => Real.sqrt (outwardDegree A x)) :=
  bellman_isoperimetric HammingCubeConcrete.B HammingCubeConcrete.B_zero
    HammingCubeConcrete.B_one HammingCubeConcrete.B_nonneg
    HammingCubeConcrete.B_two_point n A

/-- Theorem 1.1, equation (1.1); the expression at density zero is zero. -/
theorem theorem_1_1 (n : ℕ) (hn : 1 ≤ n) (A : Finset (Cube n))
    (hA : density A ≤ 1 / 2) :
    let h := fun x : Cube n =>
      if x ∈ A then ((Finset.univ.filter (fun i => flip x i ∉ A)).card : ℝ) else 0
    density A * Real.sqrt (Real.logb 2 (1 / density A)) ≤
      avg (fun x => Real.sqrt (h x)) := by
  exact (HammingCubeConcrete.B_log_lower (density A) hA).trans (profile_isoperimetric n A)

/-- Theorem 1.2 (Kahn–Park): each edge from A to B is counted once. -/
theorem theorem_1_2 (n : ℕ) (hn : 1 ≤ n) (A B W : Finset (Cube n))
    (hAB : Disjoint A B) (hAW : Disjoint A W) (hBW : Disjoint B W)
    (hcover : A ∪ B ∪ W = Finset.univ) (hA : density A = 1 / 2) :
    let edgeMeasure :=
      (∑ x ∈ A, ((Finset.univ.filter (fun i => flip x i ∈ B)).card : ℝ)) /
        (2 : ℝ) ^ n
    (1 : ℝ) / 2 ≤ edgeMeasure + Real.sqrt (n : ℝ) * density W := by
  exact theorem_1_2_of_isoperimetric n hn
    (fun S hS => theorem_1_1 n hn S hS) A B W hAB hAW hBW hcover hA

/-- Theorem 1.3, including equality for the indicator of either half-cube. -/
theorem theorem_1_3 (n : ℕ) (hn : 1 ≤ n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    let gradient := fun x : Cube n =>
      Real.sqrt (∑ i : Fin n, ((f x - f (flip x i)) / 2) ^ 2)
    let deviation := avg (fun x => |f x - avg f|)
    deviation ≤ avg gradient ∧
      (∀ (i : Fin n) (b : Bool),
        (∀ x, f x = if x i = b then 1 else 0) → deviation = avg gradient) := by
  exact theorem_1_3_of_profile HammingCubeConcrete.B (profile_isoperimetric n)
    HammingCubeConcrete.B_symmetry f hf

end HammingCube

